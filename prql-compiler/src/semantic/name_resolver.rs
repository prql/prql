use std::collections::HashSet;

use anyhow::{bail, Result};
use itertools::Itertools;

use crate::ast::ast_fold::*;
use crate::error::{Error, Reason, Span, WithErrorInfo};
use crate::{ast::*, split_var_name, Declaration};

use super::Context;

/// Runs semantic analysis on the query, using current state.
///
/// Note that this removes function declarations from AST and saves them as current context.
pub fn resolve_names(nodes: Vec<Node>, context: Option<Context>) -> Result<(Vec<Node>, Context)> {
    let context = context.unwrap_or_else(init_context);

    let mut resolver = NameResolver::new(context);

    let nodes = resolver.fold_nodes(nodes)?;

    Ok((nodes, resolver.context))
}

/// Can fold (walk) over AST and for each function call or variable find what they are referencing.
pub struct NameResolver {
    pub context: Context,

    namespace: Namespace,
}

impl NameResolver {
    fn new(context: Context) -> Self {
        NameResolver {
            context,
            namespace: Namespace::FunctionsColumns,
        }
    }
}

#[derive(Debug, Clone, Copy)]
enum Namespace {
    FunctionsColumns,
    Tables,
}

impl AstFold for NameResolver {
    // save functions declarations
    fn fold_nodes(&mut self, items: Vec<Node>) -> Result<Vec<Node>> {
        // We cut out function def, so we need to run it
        // here rather than in `fold_func_def`.
        items
            .into_iter()
            .map(|node| {
                Ok(match node.item {
                    Item::FuncDef(mut func_def) => {
                        // declare variables
                        for param in &mut func_def.named_params {
                            param.declared_at = Some(self.context.declare_func_param(param));
                        }
                        for param in &mut func_def.positional_params {
                            param.declared_at = Some(self.context.declare_func_param(param));
                        }

                        // fold body
                        func_def.body = Box::new(self.fold_node(*func_def.body)?);

                        // clear declared variables
                        self.context.scope.clear();

                        self.context.declare_func(func_def);
                        None
                    }
                    _ => Some(self.fold_node(node)?),
                })
            })
            .filter_map(|x| x.transpose())
            .try_collect()
    }

    fn fold_node(&mut self, mut node: Node) -> Result<Node> {
        let r = match node.item {
            Item::FuncCall(ref func_call) => {
                // find declaration
                node.declared_at = self.resolve_name(&func_call.name, node.span)?;

                self.fold_function_call(node)?
            }

            Item::Ident(ref ident) => {
                node.declared_at = self.resolve_name(ident, node.span)?;

                // convert ident to function without args
                let func_decl = self.context.declarations.get_func(node.declared_at);
                if func_decl.is_ok() {
                    node.item = Item::FuncCall(FuncCall::without_args(ident.clone()));
                    self.fold_function_call(node)?
                } else {
                    node
                }
            }

            item => {
                node.item = fold_item(self, item)?;
                node
            }
        };

        Ok(r)
    }

    fn fold_join_filter(&mut self, filter: JoinFilter) -> Result<JoinFilter> {
        Ok(match filter {
            JoinFilter::On(nodes) => JoinFilter::On(self.fold_nodes(nodes)?),
            JoinFilter::Using(mut nodes) => {
                for node in &mut nodes {
                    let ident = node.item.as_ident().unwrap();

                    // ensure two namespaces
                    let namespaces = self.lookup_namespaces_of(ident);
                    match namespaces.len() {
                        0 => Err(format!("Unknown variable `{ident}`")),
                        1 => Err("join using a column name must belong to both tables".to_string()),
                        _ => Ok(()),
                    }
                    .map_err(|e| Error::new(Reason::Simple(e)).with_span(node.span))?;

                    let decl = Declaration::ExternRef {
                        table: None,
                        variable: ident.to_string(),
                    };

                    let id = self.context.declare(decl, node.span);
                    self.context.scope.add(ident.clone(), id);

                    node.declared_at = Some(id);
                }
                JoinFilter::Using(nodes)
            }
        })
    }

    fn fold_table(&mut self, mut table: Table) -> Result<Table> {
        // fold pipeline
        table.pipeline = Box::new(self.fold_node(*table.pipeline)?);

        // declare table
        let decl = Declaration::Table(table.name.clone());
        table.id = Some(self.context.declare(decl, None));

        Ok(table)
    }
}

impl NameResolver {
    fn fold_function_call(&mut self, node: Node) -> Result<Node> {
        let func_call = node.item.into_func_call().unwrap();

        let id = node.declared_at;
        let func_def = self.context.declarations.get_func(id)?.clone();

        // fold params
        let outer_namespace = self.namespace;
        let mut folded = FuncCall::without_args(func_call.name);

        for (index, arg) in func_call.args.into_iter().enumerate() {
            let param = func_def.positional_params.get(index);

            folded.args.push(self.fold_function_arg(arg, param)?);
        }

        for (name, arg) in func_call.named_args {
            let param = func_def.named_params.iter().find(|p| p.name == name);

            let arg = self.fold_function_arg(*arg, param)?;
            folded.named_args.insert(name, Box::new(arg));
        }

        self.namespace = outer_namespace;
        let func_call = Item::FuncCall(folded);

        Ok(Node {
            item: func_call,
            ..node
        })
    }

    fn fold_function_arg(&mut self, mut arg: Node, param: Option<&FuncParam>) -> Result<Node> {
        match param.and_then(|p| p.ty.as_ref()) {
            Some(Ty::Unresolved) => Ok(arg),
            Some(expected) if Ty::Literal(TyLit::Table) <= *expected => {
                self.namespace = Namespace::Tables;

                let (alias, expr) = arg.clone().into_name_and_expr();
                let name = expr.unwrap(Item::into_ident, "ident").with_help(
                    "Inline tables expressions are not yet supported. You can only pass a table name.",
                )?;

                arg.declared_at = Some(self.context.declare_table(name, alias));
                Ok(arg)
            }
            Some(expected) if Ty::Assigns <= *expected => {
                self.namespace = Namespace::FunctionsColumns;

                let assigns = arg.coerce_to_vec();
                let assigns = self.fold_assigns(assigns)?;
                Ok(Item::List(assigns).into())
            }
            _ => {
                self.namespace = Namespace::FunctionsColumns;
                self.fold_node(arg)
            }
        }
    }

    fn fold_assigns(&mut self, nodes: Vec<Node>) -> Result<Vec<Node>> {
        nodes
            .into_iter()
            .map(|mut node| {
                Ok(match node.item {
                    Item::Assign(NamedExpr { name, expr }) => {
                        // introduce a new expression alias

                        let expr = self.fold_assign_expr(*expr)?;
                        let id = expr.declared_at.unwrap();

                        self.context.scope.add(name.clone(), id);

                        node.item = Item::Ident(name);
                        node.declared_at = Some(id);
                        node
                    }
                    _ => {
                        // no new names, only fold the expr
                        self.fold_assign_expr(node)?
                    }
                })
            })
            .try_collect()
    }

    fn fold_assign_expr(&mut self, node: Node) -> Result<Node> {
        let node = self.fold_node(node)?;
        Ok(match node.item {
            Item::Ident(_) => {
                // keep existing ident
                node
            }
            _ => {
                // declare new expression so it can be references from FrameColumn
                let span = node.span;
                let decl = Declaration::Expression(Box::from(node));

                let id = self.context.declare(decl, span);

                let mut placeholder: Node = Item::Ident("<unnamed>".to_string()).into();
                placeholder.declared_at = Some(id);
                placeholder
            }
        })
    }

    pub fn resolve_name(&mut self, name: &str, span: Option<Span>) -> Result<Option<usize>> {
        match self.namespace {
            Namespace::Tables => {
                // TODO: resolve tables
                Ok(None)
            }
            Namespace::FunctionsColumns => match self.lookup_name(name, span) {
                Ok(id) => Ok(Some(id)),
                Err(e) => bail!(Error::new(Reason::Simple(e)).with_span(span)),
            },
        }
    }

    pub fn lookup_name(&mut self, name: &str, span: Option<Span>) -> Result<usize, String> {
        let (namespace, variable) = split_var_name(name);

        if let Some(decls) = self.context.scope.variables.get(name) {
            // lookup the inverse index

            match decls.len() {
                0 => unreachable!("inverse index contains empty lists?"),

                // single match, great!
                1 => Ok(decls.iter().next().cloned().unwrap()),

                // ambiguous
                _ => {
                    let decls = decls
                        .iter()
                        .map(|d| self.context.declarations.get(*d))
                        .map(|d| format!("`{d}`"))
                        .join(", ");
                    Err(format!(
                        "Ambiguous reference. Could be from either of {decls}"
                    ))
                }
            }
        } else {
            let all = if namespace.is_empty() {
                "*".to_string()
            } else {
                format!("{namespace}.*")
            };

            if let Some(decls) = self.context.scope.variables.get(&all) {
                // this variable can be from a namespace that we don't know all columns of

                match decls.len() {
                    0 => unreachable!("inverse index contains empty lists?"),

                    // single match, great!
                    1 => {
                        let table_id = decls.iter().next().unwrap();

                        let decl = Declaration::ExternRef {
                            table: Some(*table_id),
                            variable: variable.to_string(),
                        };
                        let id = self.context.declare(decl, span);
                        self.context.scope.add(name.to_string(), id);

                        Ok(id)
                    }

                    // don't report ambiguous variable, database may be able to resolve them
                    _ => {
                        let decl = Declaration::ExternRef {
                            table: None,
                            variable: name.to_string(),
                        };
                        let id = self.context.declare(decl, span);

                        Ok(id)
                    }
                }
            } else {
                dbg!(&self.context);
                Err(format!("Unknown name `{name}`"))
            }
        }
    }

    pub fn lookup_namespaces_of(&mut self, variable: &str) -> HashSet<usize> {
        let mut r = HashSet::new();
        if let Some(ns) = self.context.scope.variables.get(variable) {
            r.extend(ns.clone());
        }
        if let Some(ns) = self.context.scope.variables.get("*") {
            r.extend(ns.clone());
        }
        r
    }
}

/// Loads `internal.prql` which contains type definitions of transforms
pub fn init_context() -> Context {
    use crate::parse;
    let transforms = include_str!("./transforms.prql");
    let transforms = parse(transforms).unwrap().nodes;

    let (_, context) = resolve_names(transforms, Some(Context::default())).unwrap();
    context
}

#[cfg(test)]
mod tests {
    use insta::assert_snapshot;
    use serde_yaml::from_str;

    use crate::{parse, analyze, resolve_and_translate};

    use super::*;

    #[test]
    fn test_scopes_during_from() {
        let context = init_context();

        let mut resolver = NameResolver::new(context);

        let pipeline: Node = from_str(
            r##"
            Pipeline:
              nodes:
                - FuncCall:
                    name: from
                    args:
                    - Ident: employees
                    named_args: {}
        "##,
        )
        .unwrap();
        resolver.fold_node(pipeline).unwrap();

        assert!(resolver.context.scope.variables["employees.*"].len() == 1);
    }

    #[test]
    fn test_scopes_during_select() {
        let context = init_context();

        let mut resolver = NameResolver::new(context);

        let pipeline: Node = from_str(
            r##"
            Pipeline:
              nodes:
                - FuncCall:
                    name: from
                    args:
                    - Ident: employees
                    named_args: {}
                - FuncCall:
                    name: select
                    args:
                    - List:
                        - Assign:
                            name: salary_1
                            expr:
                                Ident: salary
                        - Assign:
                            name: salary_2
                            expr:
                                Binary:
                                  left:
                                    Ident: salary_1
                                  op: Add
                                  right:
                                    Literal:
                                        Integer: 1
                        - Ident: age
                    named_args: {}
        "##,
        )
        .unwrap();
        resolver.fold_node(pipeline).unwrap();

        assert!(resolver.context.scope.variables.contains_key("salary_1"));
        assert!(resolver.context.scope.variables.contains_key("salary_2"));
        assert!(resolver.context.scope.variables.contains_key("age"));
    }

    #[test]
    fn test_variable_scoping() {
        let prql = r#"
        from employees
        select first_name
        select last_name
        "#;
        let result = parse(prql).and_then(|x| resolve_names(x.nodes, None));
        assert!(result.is_err());

        let prql = r#"
        from employees
        select [salary1 = salary, salary2 = salary1 + 1, age]
        "#;
        let result: String = parse(prql).and_then(resolve_and_translate).unwrap();
        assert_snapshot!(result, @r###"
        SELECT
          salary AS salary1,
          salary + 1 AS salary2,
          age
        FROM
          employees
        "###);
    }

    #[test]
    fn test_join_using_two_tables() {
        let prql = r#"
        from employees
        select [first_name, emp_no]
        join salaries [emp_no]
        select [first_name, salaries.salary]
        "#;
        let result = parse(prql).and_then(|x| analyze(x.nodes, None));
        result.unwrap();

        let prql = r#"
        from employees
        select first_name
        join salaries [emp_no]
        select [first_name, salaries.salary]
        "#;
        let result = parse(prql).and_then(|x| analyze(x.nodes, None));
        assert!(result.is_err());
    }

    #[test]
    fn test_ambiguous_resolve() {
        let prql = r#"
        from employees
        join salaries [emp_no]
        select first_name      # this could belong to either table!
        "#;
        let result = parse(prql).and_then(resolve_and_translate).unwrap();
        assert_snapshot!(result, @r###"
        SELECT
          first_name
        FROM
          employees
          JOIN salaries USING(emp_no)
        "###);

        let prql = r#"
        from employees
        select first_name      # this can only be from employees
        "#;
        let result = parse(prql).and_then(resolve_and_translate).unwrap();
        assert_snapshot!(result, @r###"
        SELECT
          first_name
        FROM
          employees
        "###);

        let prql = r#"
        from employees
        select [first_name, emp_no]
        join salaries [emp_no]
        select [first_name, emp_no, salary]
        "#;
        let result = parse(prql).and_then(resolve_and_translate).unwrap();
        assert_snapshot!(result, @r###"
        SELECT
          employees.first_name,
          emp_no,
          salaries.salary
        FROM
          employees
          JOIN salaries USING(emp_no)
        "###);
    }

    #[test]
    fn test_applying_group_context() {
        assert_snapshot!(parse(r#"
        from employees
        group last_name (
            sort first_name
            take 1
        )
        "#).and_then(resolve_and_translate).unwrap(), @r###"
        WITH table_0 AS (
          SELECT
            employees.*,
            ROW_NUMBER() OVER (
              PARTITION BY last_name
              ORDER BY
                first_name
            ) AS _rn
          FROM
            employees
        )
        SELECT
          table_0.*
        FROM
          table_0
        WHERE
          _rn <= 1
        "###);

        let res = parse(
            r#"
        from employees
        group last_name (
            group last_name ( aaa )
        )
        "#,
        )
        .and_then(resolve_and_translate);
        assert!(res.is_err());

        assert_snapshot!(parse(r#"
        from employees
        group last_name (
            select first_name
        )
        "#).and_then(resolve_and_translate).unwrap(), @r###"
        SELECT
          first_name
        FROM
          employees
        "###);

        assert_snapshot!(parse(r#"
        from employees
        group last_name (
            aggregate count
        )
        "#).and_then(resolve_and_translate).unwrap(), @r###"
        SELECT
          last_name,
          COUNT(*)
        FROM
          employees
        GROUP BY
          last_name
        "###);
    }
}
