//! Transform the parsed AST into a "materialized" AST, by executing functions and
//! replacing variables. The materialized AST is "flat", in the sense that it
//! contains no query-specific logic.
use crate::ast::ast_fold::*;
use crate::ast::*;
use crate::semantic;
use crate::Declaration;
use crate::Declarations;
use crate::Frame;

use anyhow::{anyhow, Result};
use itertools::zip;
use itertools::Itertools;

use crate::semantic::{split_var_name, FrameColumn};

/// Replaces all resolved functions and variables with their declarations.
pub fn materialize(
    mut pipeline: Pipeline,
    mut context: MaterializationContext,
    as_table: Option<usize>,
) -> Result<(Pipeline, MaterializedFrame, MaterializationContext)> {
    context.frame.sort.clear();
    extract_frame(&mut pipeline, &mut context)?;

    let mut m = Materializer::new(context);

    // materialize the query
    let pipeline = m.fold_pipeline(pipeline)?;
    let frame = m.context.frame.clone();

    // materialize each of the columns
    let columns = m.anchor_columns(frame.columns, as_table)?;

    let sort = m.materialize_sort(frame.sort)?;

    // rename tables for future pipelines
    if let Some(as_table) = as_table {
        m.replace_tables(frame.tables, as_table);
    }

    Ok((pipeline, MaterializedFrame { columns, sort }, m.context))
}

fn extract_frame(pipeline: &mut Pipeline, context: &mut MaterializationContext) -> Result<()> {
    for transform in &pipeline.as_transforms().unwrap_or_default() {
        context.frame.apply_transform(transform)?;
    }

    pipeline.nodes.retain(|f| {
        !matches!(
            f.item.as_transform().unwrap(),
            Transform::Select(_) | Transform::Derive(_) | Transform::Sort(_)
        )
    });
    Ok(())
}
pub struct MaterializedFrame {
    pub columns: Vec<Node>,
    pub sort: Vec<ColumnSort>,
}

#[derive(Default)]
pub struct MaterializationContext {
    /// Map of all accessible names (for each namespace)
    pub(super) frame: Frame,

    /// All declarations, mostly from [semantic::Context]
    pub(super) declarations: Declarations,
}

impl MaterializationContext {
    pub fn declare_table(&mut self, table: &str) -> usize {
        let id = self
            .declarations
            .push(Declaration::Table(table.to_string()), None);

        self.frame.tables.push(id);
        id
    }
}

impl From<semantic::Context> for MaterializationContext {
    fn from(context: semantic::Context) -> Self {
        MaterializationContext {
            frame: Frame::default(),
            declarations: context.declarations,
        }
    }
}

/// Can fold (walk) over AST and replace function calls and variable references with their declarations.
pub struct Materializer {
    pub context: MaterializationContext,
    pub remove_namespaces: bool,
}

impl Materializer {
    fn new(context: MaterializationContext) -> Self {
        Materializer {
            remove_namespaces: context.frame.tables.len() == 1,
            context,
        }
    }

    /// Looks up column declarations and replaces them with an identifiers.
    fn anchor_columns(
        &mut self,
        columns: Vec<FrameColumn>,
        as_table: Option<usize>,
    ) -> Result<Vec<Node>> {
        let mut to_replace = Vec::new();

        let res = columns
            .into_iter()
            .map(|column| {
                Ok(match column {
                    FrameColumn::Named(name, id) => {
                        let expr_node = self.materialize_declaration(id)?;

                        let name = split_var_name(&name).1.to_string();

                        let decl = Declaration::ExternRef {
                            variable: name.clone(),
                            table: as_table,
                        };
                        to_replace.push((id, decl));

                        emit_column_with_name(expr_node, name)
                    }
                    FrameColumn::Unnamed(id) => {
                        // no need to replace declaration, since it cannot be referenced again
                        self.materialize_declaration(id)?
                    }
                    FrameColumn::All(namespace) => {
                        let decl = &self.context.declarations.get(namespace);
                        let table = decl.as_table().unwrap();
                        Item::Ident(format!("{table}.*")).into()
                    }
                })
            })
            .collect::<Result<Vec<_>>>()?;

        for (id, decl) in to_replace {
            self.context.declarations.replace(id, decl);
        }

        Ok(res)
    }

    fn replace_tables(&mut self, tables: Vec<usize>, new_table: usize) {
        let new_table = self.context.declarations.get(new_table).clone();
        for id in tables {
            self.context.declarations.replace(id, new_table.clone());
        }
    }

    /// Folds the column and returns expression that can be used in select.
    /// Also returns column id and name if declaration should be replaced.
    fn materialize_sort(&mut self, sort: Vec<ColumnSort<usize>>) -> Result<Vec<ColumnSort>> {
        sort.into_iter()
            .map(|s| {
                Ok(ColumnSort {
                    column: self.materialize_declaration(s.column)?,
                    direction: s.direction,
                })
            })
            .try_collect()
    }

    fn materialize_declaration(&mut self, id: usize) -> Result<Node> {
        let decl = self.context.declarations.get(id);

        let materialized = match decl.clone() {
            Declaration::Expression(inner) => self.fold_node(*inner)?,
            Declaration::ExternRef { table, variable } => {
                let name = if let Some(table) = table {
                    let (_, var_name) = split_var_name(&variable);

                    if self.remove_namespaces {
                        var_name.to_string()
                    } else {
                        let table = &self.context.declarations.get(table);
                        let table = table.as_table().unwrap();
                        format!("{table}.{var_name}")
                    }
                } else {
                    variable
                };

                Item::Ident(name).into()
            }
            Declaration::Function(func_call) => {
                // function without arguments (a global variable)

                let body = func_call.body;

                self.fold_node(*body)?
            }
            Declaration::Table(table) => Item::Ident(format!("{table}.*")).into(),
        };

        Ok(materialized)
    }

    fn materialize_func_call(&mut self, func_call: &FuncCall, decl: Option<usize>) -> Result<Node> {
        // locate declaration
        let func_def = self.context.declarations.get_func(decl)?.clone();

        // TODO: check if the function is called recursively.

        // for each of the params, replace its declared value
        for param in func_def.named_params {
            let id = param.declared_at.unwrap();

            let value = func_call.named_args.get(&param.name).map_or_else(
                || param.default_value.unwrap().item,
                |expr| expr.item.clone(),
            );

            self.context.declarations.replace_expr(id, value.into());
        }
        for (param, arg) in zip(func_def.positional_params.iter(), func_call.args.iter()) {
            let id = param.declared_at.unwrap();
            let expr = arg.item.clone().into();
            self.context.declarations.replace_expr(id, expr);
        }

        // Now fold body as normal node
        self.fold_node(*func_def.body)
    }
}

fn emit_column_with_name(expr_node: Node, name: String) -> Node {
    // is expr_node just an ident with same name?
    let expr_ident = expr_node.item.as_ident().map(|n| split_var_name(n).1);

    if expr_ident.map(|n| n == name).unwrap_or(false) {
        // return just the ident
        expr_node
    } else {
        // return expr with new name
        Item::Assign(NamedExpr {
            expr: Box::new(expr_node),
            name,
        })
        .into()
    }
}

impl AstFold for Materializer {
    fn fold_node(&mut self, mut node: Node) -> Result<Node> {
        // We replace Items and also pass node to `inline_func_call`,
        // so we need to run this here rather than in `fold_func_call` or `fold_item`.

        Ok(match node.item {
            Item::FuncCall(func_call) => {
                let func_call = self.fold_func_call(func_call)?;

                self.materialize_func_call(&func_call, node.declared_at)?
            }

            Item::Pipeline(p) => {
                let all_transforms = p.nodes.iter().all(|f| matches!(f.item, Item::Transform(_)));

                if all_transforms {
                    // this is a frame pipeline -> just fold and keep the pipeline

                    let pipeline = fold_pipeline(self, p)?;

                    node.item = Item::Pipeline(pipeline);
                    node
                } else {
                    // this is an inline pipeline -> materialize function calls

                    let mut p = p;
                    let mut value = self.fold_node(p.nodes.remove(0))?;

                    for function in p.nodes {
                        let (function, window) = if let Item::Windowed(w) = function.item {
                            (*w.expr.clone(), Some(w))
                        } else {
                            (function, None)
                        };

                        let mut func_call = (function.item.into_func_call())
                            .map_err(|f| anyhow!("expected FuncCall, got {f:?}"))?;

                        func_call.args.push(value);
                        value = self.materialize_func_call(&func_call, function.declared_at)?;

                        if let Some(mut w) = window {
                            w.expr = Box::new(value);
                            value = Item::Windowed(w).into();
                        }
                    }
                    value
                }
            }

            Item::Ident(_) => {
                if let Some(id) = node.declared_at {
                    self.materialize_declaration(id)?
                } else {
                    node
                }
            }

            _ => {
                node.item = fold_item(self, node.item)?;
                node
            }
        })
    }
}

impl std::fmt::Debug for MaterializationContext {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "{:?}", self.declarations)
    }
}
#[cfg(test)]
mod test {

    use super::*;
    use crate::{parse, analyze, utils::diff};
    use insta::{assert_display_snapshot, assert_snapshot, assert_yaml_snapshot};
    use serde_yaml::to_string;

    fn find_pipeline(mut res: Vec<Node>) -> Pipeline {
        res.remove(res.len() - 1).coerce_to_pipeline()
    }

    fn resolve_and_materialize(query: Query) -> Result<Vec<Node>> {
        let (res, context) = analyze(query.nodes, None)?;

        let pipeline = find_pipeline(res);

        let (mat, _, _) = materialize(pipeline, context.into(), None)?;
        Ok(mat.nodes)
    }

    #[test]
    fn test_replace_variables_1() -> Result<()> {
        let query = parse(
            r#"from employees
    derive [                                         # This adds columns / variables.
      gross_salary = salary + payroll_tax,
      gross_cost =   gross_salary + benefits_cost     # Variables can use other variables.
    ]
    "#,
        )?;

        let (res, context) = analyze(query.nodes, None)?;

        let pipeline = find_pipeline(res);

        let (mat, _, _) = materialize(pipeline.clone(), context.into(), None)?;

        // We could make a convenience function for this. It's useful for
        // showing the diffs of an operation.
        assert_display_snapshot!(diff(
            &to_string(&pipeline)?,
            &to_string(&mat)?
        ),
        @r###"
        @@ -7,16 +7,3 @@
                 declared_at: 36
             ty:
               Literal: Table
        -  - Transform:
        -      Derive:
        -        - Ident: gross_salary
        -          ty: Infer
        -        - Ident: gross_cost
        -          ty: Infer
        -    ty:
        -      Function:
        -        named: {}
        -        args:
        -          - Infer
        -        return_ty:
        -          Literal: Table
        "###);

        Ok(())
    }

    #[test]
    fn test_replace_variables_2() -> Result<()> {
        let query = parse(
            r#"
func count ->  s"COUNT(*)"
func average column ->  s"AVG({column})"
func sum column ->  s"SUM({column})"

from employees
filter country == "USA"                           # Each line transforms the previous result.
derive [                                         # This adds columns / variables.
  gross_salary = salary + payroll_tax,
  gross_cost   = gross_salary + benefits_cost    # Variables can use other variables.
]
filter gross_cost > 0
group [title, country] (
    aggregate [                  # `by` are the columns to group by.
        average salary,                              # These are aggregation calcs run on each group.
        sum     salary,
        average gross_salary,
        sum     gross_salary,
        average gross_cost,
        sum_gross_cost = sum gross_cost,
        ct = count,
    ]
)
sort sum_gross_cost
filter sum_gross_cost > 200
take 20
"#,
        )?;

        let mat = resolve_and_materialize(query).unwrap();
        assert_yaml_snapshot!(&mat);

        Ok(())
    }

    #[test]
    fn test_run_functions_args() -> Result<()> {
        let query = parse(
            r#"
        func count x ->  s"count({x})"

        from employees
        aggregate [
        count salary
        ]
        "#,
        )?;

        assert_yaml_snapshot!(query.nodes, @r###"
        ---
        - FuncDef:
            name: count
            positional_params:
              - name: x
                default_value: ~
            named_params: []
            body:
              SString:
                - String: count(
                - Expr:
                    Ident: x
                - String: )
            return_ty: ~
        - Pipeline:
            nodes:
              - FuncCall:
                  name: from
                  args:
                    - Ident: employees
                  named_args: {}
              - FuncCall:
                  name: aggregate
                  args:
                    - List:
                        - FuncCall:
                            name: count
                            args:
                              - Ident: salary
                            named_args: {}
                  named_args: {}
        "###);

        let (res, context) = analyze(query.nodes, None)?;

        let pipeline = find_pipeline(res);

        let (mat, _, _) = materialize(pipeline.clone(), context.into(), None)?;

        // We could make a convenience function for this. It's useful for
        // showing the diffs of an operation.
        let diff = diff(&to_string(&pipeline.nodes)?, &to_string(&mat.nodes)?);
        assert!(!diff.is_empty());
        assert_display_snapshot!(diff, @r###"
        @@ -9,7 +9,11 @@
         - Transform:
             Aggregate:
               assigns:
        -        - Ident: "<unnamed>"
        +        - SString:
        +            - String: count(
        +            - Expr:
        +                Ident: salary
        +            - String: )
                   ty: Infer
               by: []
           ty:
        "###);

        Ok(())
    }

    #[test]
    fn test_run_functions_nested() -> Result<()> {
        let query = parse(
            r#"
        func lag_day x ->  s"lag_day_todo({x})"
        func ret x dividend_return ->  x / (lag_day x) - 1 + dividend_return

        from a
        select (ret b c)
        "#,
        )?;

        assert_yaml_snapshot!(query.nodes[2], @r###"
        ---
        Pipeline:
          nodes:
            - FuncCall:
                name: from
                args:
                  - Ident: a
                named_args: {}
            - FuncCall:
                name: select
                args:
                  - FuncCall:
                      name: ret
                      args:
                        - Ident: b
                        - Ident: c
                      named_args: {}
                named_args: {}
        "###);

        let mat = resolve_and_materialize(query).unwrap();
        assert_yaml_snapshot!(mat, @r###"
        ---
        - Transform:
            From:
              name: a
              alias: ~
              declared_at: 41
          ty:
            Literal: Table
        "###);

        Ok(())
    }

    #[test]
    fn test_run_inline_pipelines() -> Result<()> {
        let query = parse(
            r#"
        func sum x ->  s"SUM({x})"

        from a
        aggregate [one = (foo | sum), two = (foo | sum)]
        "#,
        )?;

        let (res, context) = analyze(query.nodes, None)?;

        let pipeline = find_pipeline(res);

        let (mat, _, _) = materialize(pipeline.clone(), context.into(), None)?;

        assert_snapshot!(diff(&to_string(&pipeline.nodes)?, &to_string(&mat.nodes)?), @r###"
        @@ -9,9 +9,17 @@
         - Transform:
             Aggregate:
               assigns:
        -        - Ident: one
        +        - SString:
        +            - String: SUM(
        +            - Expr:
        +                Ident: foo
        +            - String: )
                   ty: Infer
        -        - Ident: two
        +        - SString:
        +            - String: SUM(
        +            - Expr:
        +                Ident: foo
        +            - String: )
                   ty: Infer
               by: []
           ty:
        "###);

        // Test it'll run the `sum foo` function first.
        let query = parse(
            r#"
        func sum x ->  s"SUM({x})"
        func plus_one x ->  x + 1

        from a
        aggregate [a = (sum foo | plus_one)]
        "#,
        )?;

        let mat = resolve_and_materialize(query).unwrap();

        assert_yaml_snapshot!(mat, @r###"
        ---
        - Transform:
            From:
              name: a
              alias: ~
              declared_at: 40
          ty:
            Literal: Table
        - Transform:
            Aggregate:
              assigns:
                - Binary:
                    left:
                      SString:
                        - String: SUM(
                        - Expr:
                            Ident: foo
                        - String: )
                    op: Add
                    right:
                      Literal:
                        Integer: 1
                      ty:
                        Literal: Integer
                  ty: Infer
              by: []
          ty:
            Function:
              named: {}
              args:
                - Infer
              return_ty:
                Literal: Table
        "###);

        Ok(())
    }

    #[test]
    fn test_named_args() -> Result<()> {
        let query = parse(
            r#"
        func add x to:1 ->  x + to

        from foo_table
        derive [
            added = add bar to:3,
            added_default = add bar
        ]
        "#,
        )?;
        let mat = resolve_and_materialize(query).unwrap();

        assert_yaml_snapshot!(mat, @r###"
        ---
        - Transform:
            From:
              name: foo_table
              alias: ~
              declared_at: 39
          ty:
            Literal: Table
        "###);

        Ok(())
    }

    #[test]
    fn test_materialize_1() -> Result<()> {
        let query = parse(
            r#"
        func count x ->  s"count({x})"

        from employees
        aggregate [
            count salary
        ]
        "#,
        )?;

        let mat = resolve_and_materialize(query).unwrap();
        assert_yaml_snapshot!(mat,
            @r###"
        ---
        - Transform:
            From:
              name: employees
              alias: ~
              declared_at: 38
          ty:
            Literal: Table
        - Transform:
            Aggregate:
              assigns:
                - SString:
                    - String: count(
                    - Expr:
                        Ident: salary
                    - String: )
                  ty: Infer
              by: []
          ty:
            Function:
              named: {}
              args:
                - Infer
              return_ty:
                Literal: Table
        "###
        );
        Ok(())
    }

    #[test]
    fn test_materialize_2() -> Result<()> {
        let query = parse(
            r#"
func count ->  s"COUNT(*)"
func average column ->  s"AVG({column})"
func sum column ->  s"SUM({column})"

from employees
filter country == "USA"                           # Each line transforms the previous result.
derive [                                         # This adds columns / variables.
  gross_salary = salary + payroll_tax,
  gross_cost =   gross_salary + benefits_cost    # Variables can use other variables.
]
filter gross_cost > 0
group [title, country] (
    aggregate [                  # `by` are the columns to group by.
        average salary,                              # These are aggregation calcs run on each group.
        sum     salary,
        average gross_salary,
        sum     gross_salary,
        average gross_cost,
        sum_gross_cost = sum gross_cost,
        ct = count,
    ]
)
sort sum_gross_cost
filter sum_gross_cost > 200
take 20
"#,
        )?;

        let mat = resolve_and_materialize(query).unwrap();
        assert_yaml_snapshot!(mat);
        Ok(())
    }

    #[test]
    fn test_materialize_3() -> Result<()> {
        let query = parse(
            r#"
        func interest_rate ->  0.2

        func lag_day x ->  s"lag_day_todo({x})"
        func ret x dividend_return ->  x / (lag_day x) - 1 + dividend_return
        func excess x ->  (x - interest_rate) / 252
        func if_valid x ->  s"IF(is_valid_price, {x}, NULL)"

        from prices
        derive [
            return_total      = if_valid (ret prices_adj div_ret),
            return_usd        = if_valid (ret prices_usd div_ret),
            return_excess     = excess return_total,
            return_usd_excess = excess return_usd,
        ]
        select [
            date,
            sec_id,
            return_total,
            return_usd,
            return_excess,
            return_usd_excess,
        ]
        "#,
        )?;
        let mat = resolve_and_materialize(query).unwrap();
        assert_yaml_snapshot!(mat);

        Ok(())
    }

    #[test]
    fn test_variable_after_aggregate() -> Result<()> {
        let query = parse(
            r#"
        func average column ->  s"AVG({column})"

        from employees
        group [title, emp_no] (
            aggregate [emp_salary = average salary]
        )
        group [title] (
            aggregate [avg_salary = average emp_salary]
        )
        "#,
        )?;

        let mat = resolve_and_materialize(query).unwrap();
        assert_yaml_snapshot!(mat, @r###"
        ---
        - Transform:
            From:
              name: employees
              alias: ~
              declared_at: 38
          ty:
            Literal: Table
        - Transform:
            Group:
              by:
                - Ident: title
                - Ident: emp_no
              pipeline:
                Pipeline:
                  nodes:
                    - Transform:
                        Aggregate:
                          assigns:
                            - SString:
                                - String: AVG(
                                - Expr:
                                    Ident: salary
                                - String: )
                              ty: Infer
                          by:
                            - Ident: title
                            - Ident: emp_no
                      ty:
                        Function:
                          named: {}
                          args:
                            - Infer
                          return_ty:
                            Literal: Table
          ty:
            Function:
              named: {}
              args:
                - Infer
              return_ty:
                Literal: Table
        - Transform:
            Group:
              by:
                - Ident: title
              pipeline:
                Pipeline:
                  nodes:
                    - Transform:
                        Aggregate:
                          assigns:
                            - SString:
                                - String: AVG(
                                - Expr:
                                    SString:
                                      - String: AVG(
                                      - Expr:
                                          Ident: salary
                                      - String: )
                                - String: )
                              ty: Infer
                          by:
                            - Ident: title
                      ty:
                        Function:
                          named: {}
                          args:
                            - Infer
                          return_ty:
                            Literal: Table
          ty:
            Function:
              named: {}
              args:
                - Infer
              return_ty:
                Literal: Table
        "###);

        Ok(())
    }

    #[test]
    fn test_frames_and_names() -> Result<()> {
        let query1 = parse(
            r#"
        from orders
        select [customer_no, gross, tax, gross - tax]
        take 20
        "#,
        )?;

        let query2 = parse(
            r#"
        from table_1
        join customers [customer_no]
        "#,
        )?;

        let (res1, context) = analyze(query1.nodes, None)?;
        let (res2, context) = analyze(query2.nodes, Some(context))?;

        let (mat, frame, context) = materialize(find_pipeline(res1), context.into(), None)?;

        assert_yaml_snapshot!(mat.nodes, @r###"
        ---
        - Transform:
            From:
              name: orders
              alias: ~
              declared_at: 36
          ty:
            Literal: Table
        - Transform:
            Take:
              range:
                start: ~
                end:
                  Literal:
                    Integer: 20
              by: []
              sort: []
          ty:
            Function:
              named: {}
              args:
                - Infer
              return_ty:
                Literal: Table
        "###);
        assert_yaml_snapshot!(frame.columns, @r###"
        ---
        - Ident: customer_no
        - Ident: gross
        - Ident: tax
        - Binary:
            left:
              Ident: gross
            op: Sub
            right:
              Ident: tax
          ty: Infer
        "###);

        let (mat, frame, _) = materialize(find_pipeline(res2), context, None)?;

        assert_yaml_snapshot!(mat.nodes, @r###"
        ---
        - Transform:
            From:
              name: table_1
              alias: ~
              declared_at: 41
          ty:
            Literal: Table
        - Transform:
            Join:
              side: Inner
              with:
                name: customers
                alias: ~
                declared_at: 42
              filter:
                Using:
                  - Ident: customer_no
          ty:
            Function:
              named: {}
              args:
                - Infer
              return_ty:
                Literal: Table
        "###);
        assert_yaml_snapshot!(frame.columns, @r###"
        ---
        - Ident: table_1.*
        - Ident: customers.*
        - Ident: customer_no
        "###);

        Ok(())
    }
}
