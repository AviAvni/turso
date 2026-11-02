use std::sync::Arc;

use turso_parser::ast;

use crate::{
    bail_parse_error,
    namespace::{mangle_name, NamespaceId, NamespaceRef},
    schema::{BTreeTable, Table},
    security::row_security::{
        RowSecurityCatalog, RowSecurityChange, CREATE_ROW_SECURITY_TABLE_SQL,
        ROW_SECURITY_TABLE_NAME,
    },
    storage::pager::CreateBTreeFlags,
    translate::{
        collate::CollationSeq,
        emitter::Resolver,
        plan::{JoinOrigin, TableReferences, WhereTerm, WhereTermOrigin},
        schema::{emit_schema_entry, SchemaEntryType, SQLITE_TABLEID},
    },
    util::normalize_ident,
    vdbe::{
        builder::{CursorType, ProgramBuilder},
        insn::{to_u32, CmpInsFlags, Cookie, InsertFlags, Insn, RegisterOrLiteral},
    },
    Result, MAIN_DB_ID,
};

pub fn translate_row_security_change(
    namespace: NamespaceRef,
    table_name: &str,
    enable: bool,
    resolver: &Resolver,
    program: &mut ProgramBuilder,
) -> Result<()> {
    if !resolver.catalog.dialect.supports_roles() {
        bail_parse_error!("row-level security is not supported");
    }
    reject_table_outside_main(namespace)?;
    let table = stored_table_name(namespace, table_name);
    if catalog(resolver).has_row_security(&table) == enable {
        return Ok(());
    }
    let rows = RowSecurityRows::open(resolver, program)?;
    if enable {
        rows.emit_insert(program, &["row_security", "", &table, "", ""]);
    } else {
        rows.emit_delete(program, &[("row_security", 0), (&table, 2)]);
    }
    emit_catalog_update(
        program,
        resolver,
        RowSecurityChange::SetRowSecurity {
            table,
            enabled: enable,
        },
    );
    Ok(())
}

/// DROP TABLE removes the table's row-level security.
pub fn emit_drop_table_row_security_cleanup(
    table_name: &str,
    namespace: NamespaceRef,
    resolver: &Resolver,
    program: &mut ProgramBuilder,
) -> Result<()> {
    let table = stored_table_name(namespace, table_name);
    if namespace.database_id != MAIN_DB_ID || !has_row_security(&table, resolver) {
        return Ok(());
    }
    let rows = RowSecurityRows::open(resolver, program)?;
    rows.emit_delete(program, &[("row_security", 0), (&table, 2)]);
    emit_catalog_update(program, resolver, RowSecurityChange::DropTable(table));
    Ok(())
}

pub fn reject_rename_of_table_with_row_security(
    table_name: &str,
    namespace: NamespaceRef,
    resolver: &Resolver,
) -> Result<()> {
    if namespace.database_id == MAIN_DB_ID
        && has_row_security(&stored_table_name(namespace, table_name), resolver)
    {
        bail_parse_error!(
            "cannot rename table \"{table_name}\": renaming tables with row-level security is not supported"
        );
    }
    Ok(())
}

/// A role sees no rows of a table with row-level security: every such table
/// in the FROM clause gets a filter that is always false. For the right side
/// of an outer join the filter is part of the join condition, so the hidden
/// rows produce NULLs like rows that do not exist. The filters go before the
/// query's own conditions, so no expression of the query sees a hidden row.
/// The tables are recorded so the optimizer does not choose access methods
/// that evaluate the query's expressions on a row before its filter.
pub fn add_select_row_security_filters(
    table_references: &mut TableReferences,
    where_clause: &mut Vec<WhereTerm>,
    resolver: &Resolver,
) -> Result<()> {
    let mut filters = Vec::new();
    let mut filtered_tables = Vec::new();
    for table in table_references.joined_tables() {
        let Table::BTree(btree) = &table.table else {
            continue;
        };
        if !row_security_applies(&btree.declared_name, table.namespace, resolver)? {
            continue;
        }
        if table_references
            .joined_tables()
            .iter()
            .any(|table| table.join_info.as_ref().is_some_and(|j| j.is_full_outer()))
        {
            bail_parse_error!(
                "FULL JOIN with table \"{}\" that has row-level security is not supported",
                btree.declared_name
            );
        }
        filtered_tables.push(table.internal_id);
        let is_outer = table
            .join_info
            .as_ref()
            .is_some_and(|join_info| join_info.is_outer());
        filters.push(WhereTerm {
            expr: ast::Expr::Literal(ast::Literal::Numeric("0".to_string())),
            origin: if is_outer {
                WhereTermOrigin::Join(JoinOrigin::Outer(table.internal_id))
            } else {
                WhereTermOrigin::Where
            },
            consumed: false,
        });
    }
    for internal_id in filtered_tables {
        table_references.mark_row_security_filtered(internal_id);
    }
    where_clause.splice(0..0, filters);
    Ok(())
}

/// A role cannot write to a table with row-level security yet.
pub fn reject_write_with_row_security(
    table_name: &str,
    namespace: NamespaceRef,
    resolver: &Resolver,
) -> Result<()> {
    if row_security_applies(table_name, namespace, resolver)? {
        bail_parse_error!(
            "writing to table \"{table_name}\" with row-level security is not supported for roles"
        );
    }
    Ok(())
}

/// Virtual tables that read the database file directly would show the rows
/// row-level security hides.
pub fn reject_raw_storage_for_roles(table_name: &str, resolver: &Resolver) -> Result<()> {
    if resolver.row_security_role.is_some()
        && ["sqlite_dbpage", "btree_dump"]
            .iter()
            .any(|name| name.eq_ignore_ascii_case(table_name))
    {
        bail_parse_error!("permission denied: {table_name} requires the superuser");
    }
    Ok(())
}

/// Whether row-level security restricts what the statement being compiled
/// may do with `table_name`. The catalog only covers the main database.
/// Tables of attached databases that have their own catalog are rejected
/// instead of being treated as unprotected.
fn row_security_applies(
    table_name: &str,
    namespace: NamespaceRef,
    resolver: &Resolver,
) -> Result<bool> {
    if resolver.row_security_role.is_none() {
        return Ok(false);
    }
    if namespace.database_id != MAIN_DB_ID {
        let has_catalog = resolver.with_schema(namespace.database_id, |schema| {
            schema
                .get_btree_table(NamespaceId::ROOT, ROW_SECURITY_TABLE_NAME)
                .is_some()
        });
        if has_catalog {
            bail_parse_error!(
                "table \"{table_name}\" is in an attached database with row-level security, which is not supported"
            );
        }
        return Ok(false);
    }
    Ok(catalog(resolver).has_row_security(&stored_table_name(namespace, table_name)))
}

fn reject_table_outside_main(namespace: NamespaceRef) -> Result<()> {
    if namespace.database_id != MAIN_DB_ID {
        bail_parse_error!("row-level security is only supported for tables in the main database");
    }
    Ok(())
}

/// The name the catalog knows a table by: the name it is stored under in the
/// main database, which tells apart tables of the same name in different
/// schemas.
fn stored_table_name(namespace: NamespaceRef, table_name: &str) -> String {
    mangle_name(namespace.id, &normalize_ident(table_name))
}

fn has_row_security(table_name: &str, resolver: &Resolver) -> bool {
    catalog(resolver).has_row_security(table_name)
}

fn catalog(resolver: &Resolver) -> Arc<RowSecurityCatalog> {
    resolver.with_schema(MAIN_DB_ID, |schema| schema.row_security.clone())
}

/// Bumps the schema cookie and then applies `change` to the in-memory catalog.
/// The cookie goes first because writing it is what fails when the
/// transaction cannot change the schema, and a failed statement must not
/// leave the in-memory catalog changed.
fn emit_catalog_update(
    program: &mut ProgramBuilder,
    resolver: &Resolver,
    change: RowSecurityChange,
) {
    program.emit_insn(Insn::SetCookie {
        db: MAIN_DB_ID,
        cookie: Cookie::SchemaVersion,
        value: (resolver.schema().schema_version + 1) as i32,
        p5: 0,
    });
    program.emit_insn(Insn::UpdateRowSecurity {
        db: MAIN_DB_ID,
        change: Box::new(change),
    });
}

/// Write cursor on `__turso_internal_row_security`, which is created on
/// first use.
struct RowSecurityRows {
    cursor_id: usize,
}

impl RowSecurityRows {
    fn open(resolver: &Resolver, program: &mut ProgramBuilder) -> Result<Self> {
        let (table, root_page) = match resolver
            .schema()
            .get_btree_table(NamespaceId::ROOT, ROW_SECURITY_TABLE_NAME)
        {
            Some(table) => {
                let root_page = RegisterOrLiteral::Literal(table.root_page);
                (table, root_page)
            }
            None => Self::emit_create_table(resolver, program)?,
        };
        let cursor_id = program.alloc_cursor_id(CursorType::BTreeTable(table));
        program.emit_insn(Insn::OpenWrite {
            cursor_id,
            root_page,
            db: MAIN_DB_ID,
        });
        Ok(Self { cursor_id })
    }

    fn emit_create_table(
        resolver: &Resolver,
        program: &mut ProgramBuilder,
    ) -> Result<(Arc<BTreeTable>, RegisterOrLiteral<i64>)> {
        let root_reg = program.alloc_register();
        program.emit_insn(Insn::CreateBtree {
            db: MAIN_DB_ID,
            root: root_reg,
            flags: CreateBTreeFlags::new_table(),
        });
        let schema_table = resolver
            .schema()
            .get_btree_table(NamespaceId::ROOT, SQLITE_TABLEID)
            .expect("sqlite_schema always exists");
        let schema_cursor_id = program.alloc_cursor_id(CursorType::BTreeTable(schema_table));
        program.emit_insn(Insn::OpenWrite {
            cursor_id: schema_cursor_id,
            root_page: 1i64.into(),
            db: MAIN_DB_ID,
        });
        emit_schema_entry(
            program,
            resolver,
            schema_cursor_id,
            None,
            SchemaEntryType::Table,
            ROW_SECURITY_TABLE_NAME,
            ROW_SECURITY_TABLE_NAME,
            root_reg,
            Some(CREATE_ROW_SECURITY_TABLE_SQL.to_string()),
        )?;
        program.emit_insn(Insn::ParseSchema {
            db: schema_cursor_id,
            where_clause: Some(format!(
                "tbl_name = '{ROW_SECURITY_TABLE_NAME}' AND type != 'trigger'"
            )),
            trigger_target_database_id: None,
        });
        let table = Arc::new(BTreeTable::from_sql(CREATE_ROW_SECURITY_TABLE_SQL, 0)?);
        Ok((table, RegisterOrLiteral::Register(root_reg)))
    }

    fn emit_insert(&self, program: &mut ProgramBuilder, values: &[&str]) {
        let rowid_reg = program.alloc_register();
        program.emit_insn(Insn::NewRowid {
            cursor: self.cursor_id,
            rowid_reg,
            prev_largest_reg: 0,
        });
        let first_reg = program.alloc_registers(values.len());
        for (i, value) in values.iter().enumerate() {
            program.emit_insn(Insn::String8 {
                dest: first_reg + i,
                value: value.to_string(),
            });
        }
        let record_reg = program.alloc_register();
        program.emit_insn(Insn::MakeRecord {
            start_reg: to_u32(first_reg),
            count: to_u32(values.len()),
            dest_reg: to_u32(record_reg),
            index_name: None,
            affinity_str: None,
        });
        program.emit_insn(Insn::Insert {
            cursor: self.cursor_id,
            key_reg: rowid_reg,
            record_reg,
            flag: InsertFlags::new().skip_last_rowid(),
            table_name: ROW_SECURITY_TABLE_NAME.to_string(),
        });
    }

    /// Deletes every row whose columns equal the given `(value, column)` pairs.
    fn emit_delete(&self, program: &mut ProgramBuilder, matches: &[(&str, usize)]) {
        let done = program.allocate_label();
        let loop_start = program.allocate_label();
        program.emit_insn(Insn::Rewind {
            cursor_id: self.cursor_id,
            pc_if_empty: done,
        });
        program.preassign_label_to_next_insn(loop_start);
        let next = program.allocate_label();
        for (value, column) in matches {
            let column_reg = program.alloc_register();
            program.emit_column_or_rowid(self.cursor_id, *column, column_reg);
            let value_reg = program.emit_string8_new_reg(value.to_string());
            program.emit_insn(Insn::Ne {
                lhs: column_reg,
                rhs: value_reg,
                target_pc: next,
                flags: CmpInsFlags::default(),
                collation: CollationSeq::for_internal_values(),
            });
        }
        program.emit_insn(Insn::Delete {
            cursor_id: self.cursor_id,
            table_name: ROW_SECURITY_TABLE_NAME.to_string(),
            is_part_of_update: false,
        });
        program.preassign_label_to_next_insn(next);
        program.emit_insn(Insn::Next {
            cursor_id: self.cursor_id,
            pc_if_next: loop_start,
            fullscan: false,
            is_index: false,
        });
        program.preassign_label_to_next_insn(done);
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use turso_parser::ast;

    use crate::dialect::SqliteWithRolesDialect;
    use crate::{Connection, Database, DatabaseOpts, MemoryIO, OpenFlags, Value, IO};

    fn open_database(opts: DatabaseOpts) -> Arc<Database> {
        let io: Arc<dyn IO> = Arc::new(MemoryIO::new());
        Database::open_file_with_flags(
            io,
            ":memory:",
            OpenFlags::Create,
            opts,
            None,
            Arc::new(SqliteWithRolesDialect),
        )
        .unwrap()
    }

    fn open_connection() -> Arc<Connection> {
        connect(&open_database(DatabaseOpts::new()))
    }

    fn connect(db: &Arc<Database>) -> Arc<Connection> {
        db.connect(crate::ConnectOpts::new()).unwrap()
    }

    fn create_docs_with_row_security(conn: &Arc<Connection>) {
        for sql in [
            "CREATE TABLE docs(id INTEGER PRIMARY KEY, owner TEXT)",
            "INSERT INTO docs VALUES (1, 'alice'), (2, 'bob'), (3, 'alice')",
            "CREATE TABLE ids(id INTEGER)",
            "INSERT INTO ids VALUES (1), (2)",
        ] {
            conn.execute(sql).unwrap();
        }
        create_role(conn, "alice").unwrap();
        set_row_security(conn, "docs", true).unwrap();
    }

    #[test]
    fn superuser_sees_rows_of_table_with_row_security() {
        let conn = open_connection();
        create_docs_with_row_security(&conn);

        assert_eq!(
            integers(&conn, "SELECT id FROM docs ORDER BY id"),
            [1, 2, 3]
        );
    }

    #[test]
    fn role_sees_no_rows_of_table_with_row_security() {
        let conn = open_connection();
        create_docs_with_row_security(&conn);
        conn.execute("CREATE VIEW all_docs AS SELECT * FROM docs")
            .unwrap();

        set_role(&conn, "alice").unwrap();

        for sql in [
            "SELECT count(*) FROM docs",
            "SELECT count(*) FROM docs WHERE id = 1",
            "SELECT count(*) FROM (SELECT * FROM docs)",
            "WITH d AS (SELECT * FROM docs) SELECT count(*) FROM d",
            "SELECT count(*) FROM all_docs",
            "SELECT count(*) FROM ids WHERE id IN (SELECT id FROM docs)",
            "SELECT (SELECT count(*) FROM docs)",
        ] {
            assert_eq!(integers(&conn, sql), [0], "{sql}");
        }
    }

    #[test]
    fn disabled_row_security_shows_rows_again() {
        let conn = open_connection();
        create_docs_with_row_security(&conn);
        set_row_security(&conn, "docs", false).unwrap();

        set_role(&conn, "alice").unwrap();

        assert_eq!(integers(&conn, "SELECT count(*) FROM docs"), [3]);
    }

    #[test]
    fn row_security_can_change_on_table_with_materialized_view() {
        let conn = connect(&open_database(DatabaseOpts::new().with_views(true)));
        conn.execute("CREATE TABLE docs(id INTEGER PRIMARY KEY, owner TEXT)")
            .unwrap();
        conn.execute("CREATE MATERIALIZED VIEW owners AS SELECT owner FROM docs")
            .unwrap();

        set_row_security(&conn, "docs", true).unwrap();
        set_row_security(&conn, "docs", false).unwrap();
    }

    #[test]
    fn hidden_rows_are_null_on_right_side_of_left_join() {
        let conn = open_connection();
        create_docs_with_row_security(&conn);

        set_role(&conn, "alice").unwrap();

        assert_eq!(
            texts(
                &conn,
                "SELECT coalesce(docs.owner, 'none') FROM ids LEFT JOIN docs ON docs.id = ids.id ORDER BY ids.id",
            ),
            ["none", "none"]
        );
        for sql in [
            "SELECT * FROM docs FULL JOIN ids ON docs.id = ids.id",
            "SELECT * FROM ids FULL JOIN docs ON docs.id = ids.id",
        ] {
            assert_error_contains(conn.execute(sql), "FULL JOIN");
        }
    }

    #[test]
    fn role_cannot_write_to_table_with_row_security() {
        let conn = open_connection();
        create_docs_with_row_security(&conn);

        set_role(&conn, "alice").unwrap();

        for sql in [
            "INSERT INTO docs VALUES (4, 'alice')",
            "UPDATE docs SET owner = 'alice'",
            "DELETE FROM docs",
        ] {
            assert_error_contains(conn.execute(sql), "row-level security");
        }
        conn.execute("INSERT INTO ids SELECT id FROM docs").unwrap();
        conn.execute("UPDATE ids SET id = 0 FROM docs WHERE docs.id = ids.id")
            .unwrap();
        reset_role(&conn).unwrap();
        assert_eq!(integers(&conn, "SELECT id FROM ids ORDER BY id"), [1, 2]);
    }

    #[test]
    fn role_cannot_open_blob_in_table_with_row_security() {
        let conn = open_connection();
        for sql in [
            "CREATE TABLE docs(id INTEGER PRIMARY KEY, owner TEXT, payload BLOB)",
            "INSERT INTO docs VALUES (1, 'bob', x'01020304')",
            "CREATE TABLE notes(id INTEGER PRIMARY KEY, payload BLOB)",
            "INSERT INTO notes VALUES (1, x'05060708')",
        ] {
            conn.execute(sql).unwrap();
        }
        create_role(&conn, "alice").unwrap();
        set_row_security(&conn, "docs", true).unwrap();

        set_role(&conn, "alice").unwrap();

        for read_write in [false, true] {
            let error = conn
                .blob_open("docs", "payload", 1, read_write)
                .err()
                .unwrap();
            assert!(error.to_string().contains("row-level security"), "{error}");
        }
        let mut blob = conn.blob_open("notes", "payload", 1, false).unwrap();
        let mut buf = [0u8; 4];
        blob.read(0, &mut buf).unwrap();
        assert_eq!(buf, [5, 6, 7, 8]);
    }

    #[test]
    fn foreign_key_action_changes_rows_hidden_from_role() {
        let conn = open_connection();
        for sql in [
            "PRAGMA foreign_keys = ON",
            "CREATE TABLE parent(id INTEGER PRIMARY KEY)",
            "CREATE TABLE child(id INTEGER PRIMARY KEY, parent_id INTEGER REFERENCES parent(id) ON DELETE CASCADE)",
            "INSERT INTO parent VALUES (1)",
            "INSERT INTO child VALUES (1, 1)",
        ] {
            conn.execute(sql).unwrap();
        }
        create_role(&conn, "alice").unwrap();
        set_row_security(&conn, "child", true).unwrap();
        set_role(&conn, "alice").unwrap();

        conn.execute("DELETE FROM parent WHERE id = 1").unwrap();

        reset_role(&conn).unwrap();
        assert_eq!(integers(&conn, "SELECT count(*) FROM child"), [0]);
    }

    #[test]
    fn statement_prepared_by_superuser_hides_rows_from_role() {
        let conn = open_connection();
        create_docs_with_row_security(&conn);
        let mut stmt = conn.prepare("SELECT count(*) FROM docs").unwrap();

        set_role(&conn, "alice").unwrap();

        let rows = stmt.run_collect_rows().unwrap();
        assert_eq!(rows, vec![vec![Value::from_i64(0)]]);
    }

    #[test]
    fn row_security_is_seen_by_other_connections() {
        let db = open_database(DatabaseOpts::new());
        let conn = connect(&db);
        let other = connect(&db);
        integers(&other, "SELECT count(*) FROM sqlite_schema");

        create_docs_with_row_security(&conn);
        set_role(&other, "alice").unwrap();

        assert_eq!(integers(&other, "SELECT count(*) FROM docs"), [0]);
    }

    #[cfg(feature = "fs")]
    #[test]
    fn row_security_survives_reopen() {
        for mvcc in [false, true] {
            let dir = tempfile::TempDir::new().unwrap();
            let path = dir.path().join("row_security.db");
            let path = path.to_str().unwrap();
            let io: Arc<dyn IO> = Arc::new(crate::PlatformIO::new().unwrap());
            {
                let db = open_file(&io, path, DatabaseOpts::new());
                let conn = connect(&db);
                if mvcc {
                    conn.execute("PRAGMA journal_mode = 'mvcc'").unwrap();
                }
                create_docs_with_row_security(&conn);
                conn.close().unwrap();
            }

            let db = open_file(&io, path, DatabaseOpts::new());
            let conn = connect(&db);
            set_role(&conn, "alice").unwrap();

            assert_eq!(
                integers(&conn, "SELECT count(*) FROM docs"),
                [0],
                "mvcc={mvcc}"
            );
        }
    }

    #[test]
    fn drop_table_removes_row_security() {
        let conn = open_connection();
        create_docs_with_row_security(&conn);

        conn.execute("DROP TABLE docs").unwrap();

        conn.execute("CREATE TABLE docs(id INTEGER)").unwrap();
        conn.execute("INSERT INTO docs VALUES (1)").unwrap();
        set_role(&conn, "alice").unwrap();
        assert_eq!(integers(&conn, "SELECT count(*) FROM docs"), [1]);
    }

    #[test]
    fn drop_table_rejected_by_foreign_key_keeps_row_security() {
        let conn = open_connection();
        create_docs_with_row_security(&conn);
        for sql in [
            "PRAGMA foreign_keys = ON",
            "CREATE TABLE notes(doc_id INTEGER REFERENCES docs(id) ON DELETE RESTRICT)",
            "INSERT INTO notes VALUES (1)",
            "BEGIN",
        ] {
            conn.execute(sql).unwrap();
        }

        assert_error_contains(conn.execute("DROP TABLE docs"), "FOREIGN KEY");

        assert_eq!(integers(&conn, "SELECT count(*) FROM notes"), [1]);
        conn.execute("COMMIT").unwrap();
        set_role(&conn, "alice").unwrap();
        assert_eq!(integers(&conn, "SELECT count(*) FROM docs"), [0]);
    }

    #[test]
    fn drop_table_removes_only_its_own_row_security() {
        let conn = open_connection();
        conn.execute("CREATE TABLE \"\"(x)").unwrap();
        conn.execute("CREATE TABLE docs(x)").unwrap();
        set_row_security(&conn, "", true).unwrap();
        set_row_security(&conn, "docs", true).unwrap();

        conn.execute("DROP TABLE \"\"").unwrap();

        assert_eq!(
            texts(
                &conn,
                "SELECT kind || ':' || tbl_name FROM __turso_internal_row_security"
            ),
            ["row_security:docs"]
        );
    }

    #[test]
    fn rename_is_rejected_only_for_the_table_with_row_security() {
        let conn = open_connection();
        create_docs_with_row_security(&conn);

        assert_error_contains(
            conn.execute("ALTER TABLE docs RENAME TO papers"),
            "row-level security",
        );

        conn.execute("CREATE TEMP TABLE docs(id INTEGER)").unwrap();
        conn.execute("ALTER TABLE temp.docs RENAME TO papers")
            .unwrap();
    }

    #[test]
    fn row_security_only_on_tables_of_the_main_database() {
        let conn = connect(&open_database(DatabaseOpts::new().with_attach(true)));
        conn.execute("ATTACH ':memory:' AS other").unwrap();
        conn.execute("CREATE TABLE other.t(x)").unwrap();

        let alter = ast::Cmd::Stmt(ast::Stmt::AlterTable(ast::AlterTable {
            name: ast::QualifiedName::fullname(
                ast::Name::exact("other".to_string()),
                ast::Name::exact("t".to_string()),
            ),
            body: ast::AlterTableBody::RowSecurity(true),
        }));
        let result = conn
            .prepare_translated_cmd(alter, "ALTER TABLE other.t ENABLE ROW LEVEL SECURITY")
            .and_then(|mut stmt| stmt.run_ignore_rows());

        assert_error_contains(result, "main database");
        assert_error_contains(
            set_row_security(&conn, "sqlite_schema", true),
            "may not be modified",
        );
    }

    #[cfg(feature = "fs")]
    #[test]
    fn attached_database_with_row_security_is_rejected_for_roles() {
        let dir = tempfile::TempDir::new().unwrap();
        let other_path = dir.path().join("other.db");
        let io: Arc<dyn IO> = Arc::new(crate::PlatformIO::new().unwrap());
        {
            let other = open_file(&io, other_path.to_str().unwrap(), DatabaseOpts::new());
            let other_conn = connect(&other);
            create_docs_with_row_security(&other_conn);
            other_conn.close().unwrap();
        }
        let conn = connect(&open_database(DatabaseOpts::new().with_attach(true)));
        create_role(&conn, "alice").unwrap();
        conn.execute(format!("ATTACH '{}' AS other", other_path.display()))
            .unwrap();
        assert_eq!(integers(&conn, "SELECT count(*) FROM other.docs"), [3]);

        set_role(&conn, "alice").unwrap();

        assert_error_contains(
            conn.execute("SELECT * FROM other.ids"),
            "attached database with row-level security",
        );
    }

    #[cfg(feature = "cli_only")]
    #[test]
    fn role_cannot_read_database_pages() {
        let conn = open_connection();
        create_docs_with_row_security(&conn);

        set_role(&conn, "alice").unwrap();

        assert_error_contains(
            conn.execute("SELECT * FROM sqlite_dbpage"),
            "permission denied",
        );
    }

    /// Hash joins compute their keys, and multi-index scans their branch
    /// conditions, before a table's WHERE terms run. An expression that fails
    /// on a hidden row there would reveal it, so such tables use other access
    /// methods.
    #[test]
    fn query_expressions_never_run_on_hidden_rows() {
        let conn = open_connection();
        create_docs_with_row_security(&conn);
        for sql in [
            "ALTER TABLE docs ADD COLUMN body TEXT",
            "ALTER TABLE docs ADD COLUMN x INTEGER",
            "INSERT INTO docs(id, owner) SELECT value, 'bob' FROM generate_series(4, 300)",
            "UPDATE docs SET body = 'not json', x = id % 50",
            "CREATE INDEX docs_x ON docs(x)",
            "CREATE TABLE big(x INTEGER)",
            "INSERT INTO big SELECT value % 50 FROM generate_series(1, 5000)",
            "ANALYZE",
        ] {
            conn.execute(sql).unwrap();
        }

        set_role(&conn, "alice").unwrap();

        for sql in [
            "SELECT count(*) FROM big LEFT JOIN docs ON json_extract(docs.body, '$.x') = big.x",
            "SELECT count(*) FROM big JOIN docs ON json_extract(docs.body, '$.x') = big.x",
            "SELECT count(*) FROM docs JOIN big ON json_extract(docs.body, '$.x') = big.x",
            "SELECT id FROM docs WHERE id = 1 OR (x = 2 AND json_extract(body, '$.x') = 1)",
        ] {
            conn.execute(sql)
                .unwrap_or_else(|error| panic!("{sql}: {error}"));
        }
    }

    #[cfg(feature = "fs")]
    fn open_file(io: &Arc<dyn IO>, path: &str, opts: DatabaseOpts) -> Arc<Database> {
        Database::open_file_with_flags(
            io.clone(),
            path,
            OpenFlags::Create,
            opts,
            None,
            Arc::new(SqliteWithRolesDialect),
        )
        .unwrap()
    }

    fn integers(conn: &Arc<Connection>, sql: &str) -> Vec<i64> {
        query(conn, sql)
            .into_iter()
            .map(|value| match value {
                Value::Numeric(crate::Numeric::Integer(value)) => value,
                value => panic!("{sql}: expected an integer, got {value:?}"),
            })
            .collect()
    }

    fn texts(conn: &Arc<Connection>, sql: &str) -> Vec<String> {
        query(conn, sql)
            .into_iter()
            .map(|value| value.to_string())
            .collect()
    }

    /// The first column of every row of `sql`.
    fn query(conn: &Arc<Connection>, sql: &str) -> Vec<Value> {
        let mut stmt = conn.prepare(sql).unwrap();
        stmt.run_collect_rows()
            .unwrap()
            .into_iter()
            .map(|row| row.into_iter().next().unwrap())
            .collect()
    }

    fn assert_error_contains(result: crate::Result<()>, expected: &str) {
        let error = result.unwrap_err();
        assert!(
            error.to_string().contains(expected),
            "expected \"{expected}\", got: {error}"
        );
    }

    fn create_role(conn: &Arc<Connection>, name: &str) -> crate::Result<()> {
        run(
            conn,
            ast::Stmt::CreateRole {
                role_name: name.to_string(),
            },
        )
    }

    fn set_role(conn: &Arc<Connection>, name: &str) -> crate::Result<()> {
        run(
            conn,
            ast::Stmt::SetRole {
                role_name: Some(name.to_string()),
            },
        )
    }

    fn reset_role(conn: &Arc<Connection>) -> crate::Result<()> {
        run(conn, ast::Stmt::SetRole { role_name: None })
    }

    fn set_row_security(conn: &Arc<Connection>, table: &str, enable: bool) -> crate::Result<()> {
        run(
            conn,
            ast::Stmt::AlterTable(ast::AlterTable {
                name: ast::QualifiedName::single(ast::Name::exact(table.to_string())),
                body: ast::AlterTableBody::RowSecurity(enable),
            }),
        )
    }

    fn run(conn: &Arc<Connection>, stmt: ast::Stmt) -> crate::Result<()> {
        let sql = stmt.to_string();
        conn.prepare_translated_cmd(ast::Cmd::Stmt(stmt), &sql)?
            .run_ignore_rows()
    }
}
