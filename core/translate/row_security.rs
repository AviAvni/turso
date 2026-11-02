use std::sync::Arc;

use turso_parser::ast;

use crate::{
    bail_parse_error,
    namespace::{mangle_name, NamespaceId, NamespaceRef},
    schema::{BTreeTable, Table},
    security::row_security::{
        Policy, PolicyCondition, RowSecurityCatalog, RowSecurityChange,
        CREATE_ROW_SECURITY_TABLE_SQL, ROW_SECURITY_TABLE_NAME,
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

/// CREATE POLICY for the forms supported so far: a permissive SELECT (or
/// ALL) policy for every role, whose USING condition shows every row, no
/// row, or the rows whose owner column equals the current role.
pub fn translate_create_policy(
    policy: &ast::CreatePolicy,
    resolver: &Resolver,
    program: &mut ProgramBuilder,
) -> Result<()> {
    let (namespace, table) = main_btree_table(&policy.tbl_name, resolver)?;
    let stored_name = stored_table_name(namespace, &table.declared_name);
    let name = normalize_ident(policy.policy_name.as_str());
    if catalog(resolver)
        .policies(&stored_name)
        .iter()
        .any(|existing| existing.name == name)
    {
        bail_parse_error!(
            "policy \"{name}\" for table \"{}\" already exists",
            table.declared_name
        );
    }
    if policy.restrictive {
        bail_parse_error!("RESTRICTIVE policies are not supported");
    }
    if !matches!(
        policy.command,
        ast::PolicyCommand::All | ast::PolicyCommand::Select
    ) {
        bail_parse_error!("only FOR SELECT and FOR ALL policies are supported");
    }
    if !policy.roles.is_empty() {
        bail_parse_error!("only policies TO PUBLIC are supported");
    }
    if policy.check_expr.is_some() {
        bail_parse_error!("WITH CHECK is not supported");
    }
    let Some(using_expr) = &policy.using_expr else {
        bail_parse_error!("a policy needs a USING condition");
    };
    let condition = policy_condition(using_expr, &table)?;

    let (condition_value, column_name) = condition.to_row_values();
    let rows = RowSecurityRows::open(resolver, program)?;
    rows.emit_insert(
        program,
        &["policy", &name, &stored_name, condition_value, column_name],
    );
    emit_catalog_update(
        program,
        resolver,
        RowSecurityChange::CreatePolicy {
            table: stored_name,
            policy: Policy { name, condition },
        },
    );
    Ok(())
}

pub fn translate_drop_policy(
    policy_name: &ast::Name,
    tbl_name: &ast::QualifiedName,
    if_exists: bool,
    resolver: &Resolver,
    program: &mut ProgramBuilder,
) -> Result<()> {
    let (namespace, table) = main_btree_table(tbl_name, resolver)?;
    let stored_name = stored_table_name(namespace, &table.declared_name);
    let name = normalize_ident(policy_name.as_str());
    let exists = catalog(resolver)
        .policies(&stored_name)
        .iter()
        .any(|policy| policy.name == name);
    if !exists {
        if if_exists {
            return Ok(());
        }
        bail_parse_error!(
            "policy \"{name}\" for table \"{}\" does not exist",
            table.declared_name
        );
    }
    let table = stored_name;
    let rows = RowSecurityRows::open(resolver, program)?;
    rows.emit_delete(program, &[("policy", 0), (&name, 1), (&table, 2)]);
    emit_catalog_update(
        program,
        resolver,
        RowSecurityChange::DropPolicy { table, name },
    );
    Ok(())
}

/// DROP TABLE removes the table's row-level security and policies.
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
    rows.emit_delete(program, &[("policy", 0), (&table, 2)]);
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
            "cannot rename table \"{table_name}\": renaming tables with row-level security or policies is not supported"
        );
    }
    Ok(())
}

/// Policies refer to their owner column by name, so it cannot be renamed,
/// dropped or redefined.
pub fn reject_change_of_policy_column(
    table_name: &str,
    namespace: NamespaceRef,
    column_name: &str,
    resolver: &Resolver,
) -> Result<()> {
    if namespace.database_id != MAIN_DB_ID {
        return Ok(());
    }
    let column_name = normalize_ident(column_name);
    let stored_name = stored_table_name(namespace, table_name);
    let used_by_policy = catalog(resolver).policies(&stored_name).iter().any(|policy| {
        matches!(&policy.condition, PolicyCondition::OwnedByRole(column) if *column == column_name)
    });
    if used_by_policy {
        bail_parse_error!(
            "cannot change column \"{column_name}\" of table \"{table_name}\": a row-level security policy uses it"
        );
    }
    Ok(())
}

/// A role sees only the rows of a table with row-level security that one of
/// the table's policies shows: every such table in the FROM clause gets a
/// filter that combines the policies with OR, and that is always false
/// without policies. For the right side of an outer join the filter is part
/// of the join condition, so the hidden rows produce NULLs like rows that do
/// not exist. The filters go before the
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
    let mut used_columns = Vec::new();
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
        let role = resolver
            .row_security_role
            .as_deref()
            .expect("row security applies to roles");
        let catalog = catalog(resolver);
        let policies = catalog.policies(&stored_table_name(table.namespace, &btree.declared_name));
        if policies
            .iter()
            .any(|policy| policy.condition == PolicyCondition::AllRows)
        {
            continue;
        }
        let mut visible = None;
        for policy in policies {
            let PolicyCondition::OwnedByRole(column) = &policy.condition else {
                continue;
            };
            let (index, column) = btree
                .get_column(column)
                .expect("policy columns cannot be dropped");
            used_columns.push((table.internal_id, index));
            let owned = owned_by_role(table.internal_id, index, column.is_rowid_alias(), role);
            visible = Some(match visible {
                None => owned,
                Some(previous) => {
                    ast::Expr::Binary(Box::new(previous), ast::Operator::Or, Box::new(owned))
                }
            });
        }
        filtered_tables.push(table.internal_id);
        let is_outer = table
            .join_info
            .as_ref()
            .is_some_and(|join_info| join_info.is_outer());
        filters.push(WhereTerm {
            expr: visible
                .unwrap_or_else(|| ast::Expr::Literal(ast::Literal::Numeric("0".to_string()))),
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
    for (internal_id, column) in used_columns {
        table_references.mark_column_used(internal_id, column);
    }
    where_clause.splice(0..0, filters);
    Ok(())
}

/// `column = '<role>' COLLATE BINARY`: the column's own collation must not
/// make a different role's name match.
fn owned_by_role(
    table: ast::TableInternalId,
    column: usize,
    is_rowid_alias: bool,
    role: &str,
) -> ast::Expr {
    ast::Expr::Binary(
        Box::new(ast::Expr::Column {
            database: None,
            table,
            column,
            is_rowid_alias,
        }),
        ast::Operator::Equals,
        Box::new(ast::Expr::Collate(
            Box::new(ast::Expr::Literal(ast::Literal::String(format!(
                "'{}'",
                role.replace('\'', "''")
            )))),
            ast::Name::exact("BINARY".to_string()),
        )),
    )
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

/// The condition of a supported USING expression: `true`, `false`, or
/// `<column> = current_user` in either order, where `current_user` may also
/// be written as `current_user()` or `(SELECT current_user)`.
fn policy_condition(expr: &ast::Expr, table: &BTreeTable) -> Result<PolicyCondition> {
    let expr = unwrap_parens(expr);
    match expr {
        ast::Expr::Literal(ast::Literal::True) => return Ok(PolicyCondition::AllRows),
        ast::Expr::Literal(ast::Literal::False) => return Ok(PolicyCondition::NoRows),
        ast::Expr::Literal(ast::Literal::Numeric(n)) if n == "1" => {
            return Ok(PolicyCondition::AllRows)
        }
        ast::Expr::Literal(ast::Literal::Numeric(n)) if n == "0" => {
            return Ok(PolicyCondition::NoRows)
        }
        ast::Expr::Binary(lhs, ast::Operator::Equals, rhs) => {
            let (lhs, rhs) = (unwrap_parens(lhs), unwrap_parens(rhs));
            for (column, role) in [(lhs, rhs), (rhs, lhs)] {
                if is_current_user(role, table) {
                    if let Some(column) = column_of(column, table)? {
                        return Ok(PolicyCondition::OwnedByRole(column));
                    }
                }
            }
        }
        _ => {}
    }
    bail_parse_error!(
        "unsupported policy condition {expr}: only true, false and <column> = current_user are supported"
    )
}

fn unwrap_parens(expr: &ast::Expr) -> &ast::Expr {
    match expr {
        ast::Expr::Parenthesized(exprs) if exprs.len() == 1 => unwrap_parens(&exprs[0]),
        _ => expr,
    }
}

fn is_current_user(expr: &ast::Expr, table: &BTreeTable) -> bool {
    match expr {
        ast::Expr::FunctionCall {
            name,
            distinctness: None,
            args,
            order_by,
            within_group,
            filter_over,
        } => {
            name.as_str().eq_ignore_ascii_case("current_user")
                && args.is_empty()
                && order_by.is_empty()
                && within_group.is_empty()
                && filter_over.filter_clause.is_none()
                && filter_over.over_clause.is_none()
        }
        ast::Expr::Id(name) => {
            name.as_str().eq_ignore_ascii_case("current_user")
                && table.get_column(name.as_str()).is_none()
        }
        ast::Expr::Subquery(select) => single_value_of(select)
            .is_some_and(|value| is_current_user(unwrap_parens(value), table)),
        _ => false,
    }
}

/// The expression of `SELECT <expr>` without FROM or any other clause.
fn single_value_of(select: &ast::Select) -> Option<&ast::Expr> {
    if select.with.is_some()
        || !select.body.compounds.is_empty()
        || !select.order_by.is_empty()
        || select.limit.is_some()
    {
        return None;
    }
    match &select.body.select {
        ast::OneSelect::Select {
            distinctness: None,
            columns,
            from: None,
            where_clause: None,
            group_by: None,
            window_clause,
        } if window_clause.is_empty() => match columns.as_slice() {
            [ast::ResultColumn::Expr(expr, _)] => Some(expr),
            _ => None,
        },
        _ => None,
    }
}

/// The name of the column `expr` refers to, written as `column` or
/// `table.column`. Virtual generated columns are rejected.
fn column_of(expr: &ast::Expr, table: &BTreeTable) -> Result<Option<String>> {
    let name = match expr {
        ast::Expr::Id(name) => name,
        ast::Expr::Qualified(qualifier, name)
            if normalize_ident(qualifier.as_str()) == normalize_ident(&table.declared_name) =>
        {
            name
        }
        _ => return Ok(None),
    };
    let Some((_, column)) = table.get_column(name.as_str()) else {
        bail_parse_error!("no such column: {}", name.as_str());
    };
    if column.is_virtual_generated() {
        bail_parse_error!(
            "generated column \"{}\" cannot be a policy owner column",
            name.as_str()
        );
    }
    Ok(Some(normalize_ident(name.as_str())))
}

/// Whether the table has row-level security or policies.
fn has_row_security(table_name: &str, resolver: &Resolver) -> bool {
    let catalog = catalog(resolver);
    catalog.has_row_security(table_name) || !catalog.policies(table_name).is_empty()
}

fn main_btree_table(
    name: &ast::QualifiedName,
    resolver: &Resolver,
) -> Result<(NamespaceRef, Arc<BTreeTable>)> {
    if !resolver.catalog.dialect.supports_roles() {
        bail_parse_error!("row-level security is not supported");
    }
    let namespace = resolver.resolve_existing_table(name)?;
    reject_table_outside_main(namespace)?;
    match resolver
        .schema()
        .get_btree_table(namespace.id, name.name.as_str())
    {
        Some(table) => Ok((namespace, table)),
        None => bail_parse_error!("no such table: {}", name.name.as_str()),
    }
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

    use crate::dialect::{Dialect, SqliteWithRolesDialect};
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

    fn create_docs_with_owner_policy(conn: &Arc<Connection>) {
        create_docs_with_row_security(conn);
        create_role(conn, "bob").unwrap();
        create_policy(conn, policy("own", "docs", "owner = current_user")).unwrap();
    }

    #[test]
    fn owner_policy_shows_rows_owned_by_role() {
        let conn = open_connection();
        create_docs_with_owner_policy(&conn);

        set_role(&conn, "alice").unwrap();

        for sql in [
            "SELECT id FROM docs ORDER BY id",
            "SELECT d.id FROM docs AS d ORDER BY d.id",
            "SELECT id FROM docs WHERE id IN (1, 2, 3) ORDER BY id",
            "SELECT docs.id FROM ids JOIN docs ON docs.id >= ids.id WHERE ids.id = 1 ORDER BY docs.id",
            "WITH d AS (SELECT * FROM docs) SELECT id FROM d ORDER BY id",
        ] {
            assert_eq!(integers(&conn, sql), [1, 3], "{sql}");
        }
        assert_eq!(
            integers(&conn, "SELECT count(*) FROM docs WHERE id = 2"),
            [0]
        );
        set_role(&conn, "bob").unwrap();
        assert_eq!(integers(&conn, "SELECT id FROM docs"), [2]);
    }

    #[test]
    fn owner_policy_accepts_supabase_spellings() {
        for using in [
            "current_user = owner",
            "docs.owner = current_user()",
            "(SELECT current_user) = owner",
            "((owner) = (SELECT current_user()))",
        ] {
            let conn = open_connection();
            create_docs_with_row_security(&conn);
            create_policy(&conn, policy("own", "docs", using)).unwrap();

            set_role(&conn, "alice").unwrap();

            assert_eq!(
                integers(&conn, "SELECT id FROM docs ORDER BY id"),
                [1, 3],
                "{using}"
            );
        }
    }

    #[test]
    fn policies_combine_with_or() {
        let conn = open_connection();
        create_docs_with_owner_policy(&conn);
        conn.execute("ALTER TABLE docs ADD COLUMN editor TEXT")
            .unwrap();
        conn.execute("UPDATE docs SET editor = 'alice' WHERE id = 2")
            .unwrap();
        let mut edit = policy("edit", "docs", "editor = current_user");
        edit.command = ast::PolicyCommand::Select;
        create_policy(&conn, edit).unwrap();
        create_policy(&conn, policy("none", "docs", "false")).unwrap();

        set_role(&conn, "alice").unwrap();
        assert_eq!(
            integers(&conn, "SELECT id FROM docs ORDER BY id"),
            [1, 2, 3]
        );

        reset_role(&conn).unwrap();
        create_policy(&conn, policy("everything", "docs", "true")).unwrap();
        set_role(&conn, "bob").unwrap();
        assert_eq!(
            integers(&conn, "SELECT id FROM docs ORDER BY id"),
            [1, 2, 3]
        );
    }

    #[test]
    fn owner_policy_compares_role_names_exactly() {
        let conn = open_connection();
        conn.execute("CREATE TABLE docs(id INTEGER PRIMARY KEY, owner TEXT COLLATE NOCASE)")
            .unwrap();
        conn.execute("INSERT INTO docs VALUES (1, 'alice'), (2, 'ALICE')")
            .unwrap();
        create_role(&conn, "alice").unwrap();
        set_row_security(&conn, "docs", true).unwrap();
        create_policy(&conn, policy("own", "docs", "owner = current_user")).unwrap();

        set_role(&conn, "alice").unwrap();

        assert_eq!(integers(&conn, "SELECT id FROM docs"), [1]);
    }

    #[test]
    fn owner_policy_uses_index_on_owner_column() {
        let conn = open_connection();
        create_docs_with_owner_policy(&conn);
        conn.execute("CREATE INDEX docs_owner ON docs(owner)")
            .unwrap();

        set_role(&conn, "alice").unwrap();

        let plan = conn
            .prepare("EXPLAIN QUERY PLAN SELECT id FROM docs")
            .unwrap()
            .run_collect_rows()
            .unwrap();
        assert!(
            plan.iter()
                .any(|row| row[3].to_string().contains("docs_owner")),
            "{plan:?}"
        );
        assert_eq!(integers(&conn, "SELECT id FROM docs ORDER BY id"), [1, 3]);
    }

    #[test]
    fn unsupported_policies_are_rejected() {
        let conn = open_connection();
        create_docs_with_row_security(&conn);
        let restrictive = ast::CreatePolicy {
            restrictive: true,
            ..policy("p", "docs", "true")
        };
        let for_insert = ast::CreatePolicy {
            command: ast::PolicyCommand::Insert,
            using_expr: None,
            check_expr: Some(Box::new(expr("true"))),
            ..policy("p", "docs", "true")
        };
        let to_role = ast::CreatePolicy {
            roles: vec![ast::Name::exact("alice".to_string())],
            ..policy("p", "docs", "true")
        };
        let with_check = ast::CreatePolicy {
            check_expr: Some(Box::new(expr("true"))),
            ..policy("p", "docs", "true")
        };
        let without_using = ast::CreatePolicy {
            using_expr: None,
            ..policy("p", "docs", "true")
        };
        for (policy, expected) in [
            (restrictive, "RESTRICTIVE"),
            (for_insert, "FOR SELECT"),
            (to_role, "TO PUBLIC"),
            (with_check, "WITH CHECK"),
            (without_using, "USING"),
            (
                policy("p", "docs", "owner = 'alice'"),
                "unsupported policy condition",
            ),
            (
                policy("p", "docs", "owner = current_user AND id > 1"),
                "unsupported policy condition",
            ),
            (
                policy("p", "docs", "owner IN (SELECT current_user)"),
                "unsupported policy condition",
            ),
            (
                policy("p", "docs", "missing = current_user"),
                "no such column",
            ),
            (policy("p", "nope", "true"), "no such table"),
        ] {
            assert_error_contains(create_policy(&conn, policy), expected);
        }
        create_policy(&conn, policy("p", "docs", "true")).unwrap();
        assert_error_contains(
            create_policy(&conn, policy("p", "docs", "true")),
            "already exists",
        );
    }

    #[test]
    fn policy_owner_column_cannot_be_generated() {
        let conn = open_connection();
        conn.execute("CREATE TABLE g(a TEXT, b TEXT AS (a || ''))")
            .unwrap();

        assert_error_contains(
            create_policy(&conn, policy("p", "g", "b = current_user")),
            "generated column",
        );
    }

    #[test]
    fn policies_have_no_effect_without_row_security() {
        let conn = open_connection();
        create_docs_with_owner_policy(&conn);
        set_row_security(&conn, "docs", false).unwrap();

        set_role(&conn, "alice").unwrap();

        assert_eq!(
            integers(&conn, "SELECT id FROM docs ORDER BY id"),
            [1, 2, 3]
        );
    }

    #[test]
    fn drop_policy_hides_the_rows_it_showed() {
        let conn = open_connection();
        create_docs_with_owner_policy(&conn);

        drop_policy(&conn, "own", "docs", false).unwrap();

        assert_error_contains(drop_policy(&conn, "own", "docs", false), "does not exist");
        drop_policy(&conn, "own", "docs", true).unwrap();
        set_role(&conn, "alice").unwrap();
        assert_eq!(integers(&conn, "SELECT count(*) FROM docs"), [0]);
    }

    #[test]
    fn policies_are_seen_by_other_connections() {
        let db = open_database(DatabaseOpts::new());
        let conn = connect(&db);
        let other = connect(&db);
        integers(&other, "SELECT count(*) FROM sqlite_schema");

        create_docs_with_owner_policy(&conn);
        set_role(&other, "alice").unwrap();

        assert_eq!(integers(&other, "SELECT id FROM docs ORDER BY id"), [1, 3]);
    }

    #[cfg(feature = "fs")]
    #[test]
    fn policies_survive_reopen() {
        for mvcc in [false, true] {
            let dir = tempfile::TempDir::new().unwrap();
            let path = dir.path().join("policies.db");
            let path = path.to_str().unwrap();
            let io: Arc<dyn IO> = Arc::new(crate::PlatformIO::new().unwrap());
            {
                let db = open_file(&io, path, DatabaseOpts::new());
                let conn = connect(&db);
                if mvcc {
                    conn.execute("PRAGMA journal_mode = 'mvcc'").unwrap();
                }
                create_docs_with_owner_policy(&conn);
                conn.close().unwrap();
            }

            let db = open_file(&io, path, DatabaseOpts::new());
            let conn = connect(&db);
            set_role(&conn, "alice").unwrap();

            assert_eq!(
                integers(&conn, "SELECT id FROM docs ORDER BY id"),
                [1, 3],
                "mvcc={mvcc}"
            );
        }
    }

    #[test]
    fn policy_owner_column_cannot_change() {
        let conn = open_connection();
        create_docs_with_owner_policy(&conn);

        for sql in [
            "ALTER TABLE docs RENAME COLUMN owner TO author",
            "ALTER TABLE docs DROP COLUMN owner",
            "ALTER TABLE docs RENAME TO papers",
        ] {
            assert_error_contains(conn.execute(sql), "row-level security");
        }
        conn.execute("ALTER TABLE docs ADD COLUMN title TEXT")
            .unwrap();
        conn.execute("ALTER TABLE docs RENAME COLUMN title TO name")
            .unwrap();
        conn.execute("CREATE TEMP TABLE docs(id INTEGER, owner TEXT)")
            .unwrap();
        conn.execute("ALTER TABLE temp.docs RENAME COLUMN owner TO author")
            .unwrap();
    }

    #[test]
    fn drop_table_removes_policies() {
        let conn = open_connection();
        create_docs_with_owner_policy(&conn);

        conn.execute("DROP TABLE docs").unwrap();

        assert!(texts(
            &conn,
            "SELECT kind FROM __turso_internal_row_security WHERE tbl_name = 'docs'"
        )
        .is_empty());
        conn.execute("CREATE TABLE docs(id INTEGER, owner TEXT)")
            .unwrap();
        create_policy(&conn, policy("own", "docs", "true")).unwrap();
    }

    #[test]
    fn owner_policy_runs_before_multi_index_branch_conditions() {
        let conn = open_connection();
        create_docs_with_owner_policy(&conn);
        for sql in [
            "ALTER TABLE docs ADD COLUMN body TEXT",
            "ALTER TABLE docs ADD COLUMN x INTEGER",
            "UPDATE docs SET body = '{\"x\": 1}', x = id",
            "UPDATE docs SET body = 'not json' WHERE id = 2",
            "CREATE INDEX docs_x ON docs(x)",
        ] {
            conn.execute(sql).unwrap();
        }

        set_role(&conn, "alice").unwrap();

        assert_eq!(
            integers(
                &conn,
                "SELECT id FROM docs WHERE id = 1 OR (x = 2 AND json_extract(body, '$.x') = 1)"
            ),
            [1]
        );
    }

    /// A query's own conditions must never run on a hidden row, or an error
    /// they raise, such as malformed JSON, would reveal the row. The policy
    /// filter is evaluated before them in every query shape.
    #[test]
    fn query_conditions_never_see_hidden_rows() {
        let conn = open_connection();
        create_docs_with_owner_policy(&conn);
        for sql in [
            "ALTER TABLE docs ADD COLUMN body TEXT",
            "UPDATE docs SET body = '{\"x\": 1}'",
            "UPDATE docs SET body = 'not json' WHERE id = 2",
        ] {
            conn.execute(sql).unwrap();
        }
        let hidden_row_query = "SELECT id FROM docs WHERE json_extract(body, '$.x') = 1";
        assert_error_contains(conn.execute(hidden_row_query), "malformed JSON");

        set_role(&conn, "alice").unwrap();

        let queries = [
            hidden_row_query,
            "SELECT id FROM docs WHERE id = 2 AND json_extract(body, '$.x') = 1",
            "SELECT id FROM docs WHERE json_extract(body, '$.x') = 1 AND id > 0",
            "SELECT docs.id FROM ids JOIN docs ON docs.id = ids.id WHERE json_extract(docs.body, '$.x') = 1",
            "SELECT docs.id FROM docs JOIN ids ON docs.id = ids.id WHERE json_extract(docs.body, '$.x') = 1",
            "SELECT ids.id FROM ids LEFT JOIN docs ON docs.id = ids.id AND json_extract(docs.body, '$.x') = 1",
            "SELECT id FROM (SELECT * FROM docs) WHERE json_extract(body, '$.x') = 1",
            "SELECT id FROM docs WHERE EXISTS (SELECT 1 WHERE json_extract(docs.body, '$.x') = 1)",
            "SELECT json_extract(body, '$.x') FROM docs",
            "SELECT id FROM docs ORDER BY json_extract(body, '$.x')",
            "SELECT count(*) FROM docs GROUP BY json_extract(body, '$.x')",
        ];
        for sql in queries {
            conn.execute(sql)
                .unwrap_or_else(|error| panic!("{sql}: {error}"));
        }
        reset_role(&conn).unwrap();
        conn.execute("CREATE INDEX docs_owner ON docs(owner)")
            .unwrap();
        set_role(&conn, "alice").unwrap();
        for sql in queries {
            conn.execute(sql)
                .unwrap_or_else(|error| panic!("with index, {sql}: {error}"));
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

    /// A permissive policy for every role and every command.
    fn policy(name: &str, table: &str, using: &str) -> ast::CreatePolicy {
        ast::CreatePolicy {
            policy_name: ast::Name::exact(name.to_string()),
            tbl_name: ast::QualifiedName::single(ast::Name::exact(table.to_string())),
            restrictive: false,
            command: ast::PolicyCommand::All,
            roles: Vec::new(),
            using_expr: Some(Box::new(expr(using))),
            check_expr: None,
        }
    }

    /// The expression `sql`, parsed as the result column of a SELECT.
    fn expr(sql: &str) -> ast::Expr {
        let (Some(ast::Cmd::Stmt(ast::Stmt::Select(select))), _) = crate::dialect::SqliteDialect
            .parse(&format!("SELECT {sql}"))
            .unwrap()
        else {
            panic!("not a SELECT: {sql}");
        };
        let ast::OneSelect::Select { mut columns, .. } = select.body.select else {
            panic!("not a SELECT: {sql}");
        };
        let ast::ResultColumn::Expr(expr, _) = columns.remove(0) else {
            panic!("not an expression: {sql}");
        };
        *expr
    }

    fn create_policy(conn: &Arc<Connection>, policy: ast::CreatePolicy) -> crate::Result<()> {
        run(conn, ast::Stmt::CreatePolicy(Box::new(policy)))
    }

    fn drop_policy(
        conn: &Arc<Connection>,
        name: &str,
        table: &str,
        if_exists: bool,
    ) -> crate::Result<()> {
        run(
            conn,
            ast::Stmt::DropPolicy {
                if_exists,
                policy_name: ast::Name::exact(name.to_string()),
                tbl_name: ast::QualifiedName::single(ast::Name::exact(table.to_string())),
            },
        )
    }

    fn run(conn: &Arc<Connection>, stmt: ast::Stmt) -> crate::Result<()> {
        let sql = stmt.to_string();
        conn.prepare_translated_cmd(ast::Cmd::Stmt(stmt), &sql)?
            .run_ignore_rows()
    }
}
