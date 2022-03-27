//! This module contains the parser, which is responsible for converting a tree
//! of pest pairs into a tree of AST Items. It has a small function to call into
//! pest to get the parse tree / concrete syntaxt tree, and then a large
//! function for turning that into PRQL AST.
use super::ast::*;
use super::utils::*;
use anyhow::{anyhow, bail, Context, Result};
use itertools::Itertools;
use pest::iterators::Pairs;
use pest::Parser;
use pest_derive::Parser;

#[derive(Parser)]
#[grammar = "prql.pest"]
struct PrqlParser;

/// Build an AST from a PRQL query string.
pub fn parse(string: &str) -> Result<Item> {
    ast_of_string(string, Rule::query)
}

/// Parse a string into an AST. Unlike [parse], this can start from any rule.
fn ast_of_string(string: &str, rule: Rule) -> Result<Item> {
    parse_tree_of_str(string, rule)
        .and_then(ast_of_parse_tree)
        .and_then(|x| x.into_only())
}

/// Parse a string into a parse tree / concrete syntax tree, made up of pest Pairs.
fn parse_tree_of_str(source: &str, rule: Rule) -> Result<Pairs<Rule>> {
    Ok(PrqlParser::parse(rule, source)?)
}

/// Parses a parse tree of pest Pairs into an AST.
fn ast_of_parse_tree(pairs: Pairs<Rule>) -> Result<Vec<Item>> {
    pairs
        // Exclude end-of-input at the moment.
        .filter(|pair| pair.as_rule() != Rule::EOI)
        .map(|pair| {
            // TODO: Probably wrap each of the individual branches in a Result,
            // and don't have this wrapping `Ok`. Then move some of the panics
            // to `Err`s.
            Ok(match pair.as_rule() {
                Rule::query => Item::Query(Query {
                    items: ast_of_parse_tree(pair.into_inner())?,
                }),
                Rule::list => Item::List(
                    ast_of_parse_tree(pair.into_inner())?
                        .into_iter()
                        // This could simply be:
                        //   ListItem(expr.into_inner_items()))
                        // but we want to confirm it's an Expr, it would be a
                        // difficult mistake to catch otherwise.
                        .map(|expr| match expr {
                            Item::NamedExpr(_) => ListItem(expr.into_named_expr().unwrap()),
                            _ => unreachable!(),
                        })
                        .collect(),
                ),
                Rule::expr | Rule::expr_simple => {
                    ast_of_parse_tree(pair.into_inner())?.into_expr()
                }
                Rule::named_arg => {
                    let parsed: [Item; 2] = ast_of_parse_tree(pair.into_inner())?
                        .try_into()
                        .map_err(|e| anyhow!("Expected two items; {e:?}"))?;
                    let [name, arg] = parsed;
                    Item::NamedArg(NamedArg {
                        name: name.into_ident()?,
                        arg: Box::new(arg),
                    })
                }
                Rule::named_expr | Rule::named_expr_simple => {
                    let items = ast_of_parse_tree(pair.into_inner())?;

                    // Split the pair into its first value, which is always an Ident,
                    // and its other values.
                    let (alias, expr) = match &items[..] {
                        [Item::Ident(name), item] => {
                            (Some(name.clone()), item)
                        }
                        [item] => {
                            (None, item)
                        }
                        _ => bail!("Expected named_expr to have an expression and some identifier. Got {items:?}")
                    };
                    Item::NamedExpr(NamedExpr {
                        alias,
                        expr: Box::new(expr.clone()),
                    })
                }
                Rule::transformation => {
                    let parsed = ast_of_parse_tree(pair.into_inner())?;
                    Item::Transformation(parsed.try_into()?)
                }
                Rule::func_def => {
                    let parsed = ast_of_parse_tree(pair.into_inner())?;

                    let (name, parsed) = parsed
                        .split_first()
                        .ok_or_else(|| anyhow!("Expected at least one item"))?;

                    let name = name.clone().into_ident()?;

                    let (params, body) = if let Some((Item::Expr(params), body)) = parsed.split_first(){
                        (params, body)
                    } else {
                        unreachable!("expected function params and body, got {parsed:?}")
                    };

                    let positional_params = params
                        .iter()
                        .filter_map(|x| x.as_ident())
                        .cloned()
                        .collect();
                    let named_params = params
                        .iter()
                        .filter_map(|x| x.as_named_arg())
                        .cloned()
                        .collect();

                    Item::FuncDef(FuncDef {
                        name,
                        positional_params,
                        named_params,
                        body: Box::from(body.into_only().cloned()?),
                    })
                }
                Rule::func_def_params => Item::Expr(ast_of_parse_tree(pair.into_inner())?),
                Rule::func_call | Rule::func_curry  => {
                    let items = ast_of_parse_tree(pair.into_inner())?;

                    let (name, params) = items
                        .split_first()
                        .ok_or_else(|| anyhow!("Expected at least one item"))?;

                    let name = name.clone().into_ident()?;

                    let (named, args): (Vec<_>, Vec<_>) =
                        params.iter().partition(|x| matches!(x, Item::NamedArg(_)));

                    let args = args.into_iter().cloned().collect();

                    let named_args = named
                        .into_iter()
                        .cloned()
                        .map(|x| x.into_named_arg())
                        .try_collect()?;

                    Item::FuncCall(FuncCall {
                        name,
                        args,
                        named_args,
                    })
                },
                Rule::table => {
                    let parsed = ast_of_parse_tree(pair.into_inner())?;
                    let [name, pipeline]: [Item; 2] = parsed
                        .try_into()
                        .map_err(|e| anyhow!("Expected two items; {e:?}"))?;
                    Item::Table(Table {
                        name: name.into_ident()?,
                        pipeline: pipeline.into_pipeline()?,
                    })
                }
                Rule::ident => Item::Ident(pair.as_str().to_string()),
                // Pull out the string itself, which doesn't have the quotes
                Rule::string_literal => ast_of_parse_tree(pair.clone().into_inner())?
                    .into_iter()
                    .next()
                    .ok_or_else(|| anyhow!("Failed reading string {pair:?}"))?,
                Rule::string => Item::String(pair.as_str().to_string()),
                Rule::s_string => Item::SString(
                    pair.into_inner()
                        .map(|x| Ok::<_, anyhow::Error>(match x.as_rule() {
                            Rule::s_string_string => SStringItem::String(x.as_str().to_string()),
                            _ => SStringItem::Expr(
                                ast_of_parse_tree(x.into_inner())?.into_expr()
                            ),
                        }))
                        .try_collect()?,
                ),
                Rule::pipeline => Item::Pipeline({
                    ast_of_parse_tree(pair.into_inner())?
                        .into_iter()
                        .map(|x| match x {
                            Item::Transformation(transformation) => transformation,
                            _ => unreachable!("{x:?}"),
                        })
                        .collect()
                }),
                Rule::inline_pipeline => {
                    let parsed = ast_of_parse_tree(pair.into_inner())?;

                    let (value, func_curries) = (parsed.split_first())
                        .context("empty inline pipeline?")?;

                    let functions = func_curries.iter().cloned().map(|x| x.into_func_call()).try_collect()?;

                    Item::InlinePipeline(InlinePipeline {
                        value: Box::from(value.clone()),
                        functions
                    })
                }
                Rule::operator | Rule::number | Rule::all => Item::Raw(pair.as_str().to_owned()),
                _ => (Item::Todo(pair.as_str().to_owned())),
            })
        })
        .collect()
}

// We put this outside the main ast_of_parse_tree function to reduce the size of
// that function.
impl TryFrom<Vec<Item>> for Transformation {
    type Error = anyhow::Error;
    fn try_from(items: Vec<Item>) -> Result<Self> {
        let (name, args) = items
            .split_first()
            .ok_or_else(|| anyhow!("Expected at least one item"))?;

        let positional: Vec<NamedExpr> = args
            .iter()
            .filter_map(|x| x.as_named_expr())
            .cloned()
            .collect();

        let named: Vec<NamedArg> = args
            .iter()
            .filter_map(|x| x.as_named_arg())
            .cloned()
            .collect();

        let name = name.clone().into_ident()?;
        match name.as_str() {
            "from" => {
                let named_expr = positional.into_only()
                    .context("Expected from to have exactly one argument.\n  Hint: you can pass it as `from table_name` or `from table_name ~ my_alias`")?;

                let table_ref = TableRef {
                    name: named_expr.expr.into_ident()
                        .map_err(|_| anyhow!("From does not support inline expression. You can only pass table name."))?,
                    alias: named_expr.alias,
                };

                Ok(Transformation::From(table_ref))
            }
            "select" => Ok(Transformation::Select(
                positional
                    .into_only()
                    .context("Expected exactly one argument for `select`")?
                    .coerce_to_named_list(),
            )),
            "filter" => {
                let items = positional.into_only()?.discard_name()?.coerce_to_list();
                Ok(Transformation::Filter(Filter(items)))
            }
            "derive" => {
                let assigns = (positional)
                    .into_only()
                    .context("Expected exactly one argument for `derive`")?
                    .coerce_to_named_list();
                Ok(Transformation::Derive(assigns))
            }
            "aggregate" => {
                // TODO: redo, generalizing with checks on custom functions.
                // Ideally we'd be able to add to the error message with context
                // without falling afowl of the borrow rules.
                // Err(anyhow!(
                //     "Expected exactly one unnamed argument for aggregate, got {:?}",
                //     args
                // ))
                // })?;
                let [by] = require_named_args(named, ["by"])?;
                let by = by.map(|x| x.coerce_to_list()).unwrap_or_default();

                let select = positional
                    .into_only()
                    .map(|x| x.coerce_to_named_list())
                    .unwrap_or_default();

                Ok(Transformation::Aggregate { by, select })
            }
            "sort" => {
                let by = positional.into_only()?.discard_name()?.coerce_to_list();
                Ok(Transformation::Sort(by))
            }
            "take" => {
                // TODO: coerce to number
                let expr = positional.into_only()?.discard_name()?;
                Ok(Transformation::Take(expr.into_raw()?.parse()?))
            }
            "join" => {
                let [side] = require_named_args(named, ["side"])?;
                let side = if let Some(side) = side {
                    match side.into_ident()?.as_str() {
                        "inner" => JoinSide::Inner,
                        "left" => JoinSide::Left,
                        "right" => JoinSide::Right,
                        "full" => JoinSide::Full,
                        unknown => bail!("unknown join side: {unknown}"),
                    }
                } else {
                    JoinSide::Inner
                };

                let with = (positional.get(0).cloned())
                    .context("join requires a table name to join with")?;
                let with = (with.discard_name()?.into_ident())
                    .map_err(|x| anyhow!("join requires a table name to join with, got {x:?}"))?;

                let on = if let Some(x) = positional.get(1) {
                    x.clone().discard_name()?.coerce_to_list()
                } else {
                    vec![]
                };

                Ok(Transformation::Join { side, with, on })
            }
            _ => bail!("Expected a known transformation; got {name}"),
        }
    }
}

/// Compares expected and passed function parameters
fn require_named_args<const COUNT: usize>(
    passed: Vec<NamedArg>,
    expected: [&str; COUNT],
) -> Result<[Option<Item>; COUNT]> {
    const NONE: Option<Item> = None;
    let mut res = [NONE; COUNT];

    for p in passed {
        if let Some((pos, _)) = expected.iter().find_position(|x| x == &&p.name) {
            res[pos] = Some(*p.arg);
        } else {
            bail!("Unexpected argument '{}' with value '{:?}'", p.name, p.arg);
        }
    }
    Ok(res)
}

#[cfg(test)]
mod test {

    use super::*;
    use insta::{assert_debug_snapshot, assert_yaml_snapshot};

    #[test]
    fn test_parse_take() -> Result<()> {
        assert!(parse_tree_of_str("take 10", Rule::transformation).is_ok());
        assert!(ast_of_string("take", Rule::transformation).is_err());
        Ok(())
    }

    #[test]
    fn test_parse_string() -> Result<()> {
        assert_debug_snapshot!(parse_tree_of_str(r#"" U S A ""#, Rule::string_literal)?, @r###"
        [
            Pair {
                rule: string_literal,
                span: Span {
                    str: "\" U S A \"",
                    start: 0,
                    end: 9,
                },
                inner: [
                    Pair {
                        rule: string,
                        span: Span {
                            str: " U S A ",
                            start: 1,
                            end: 8,
                        },
                        inner: [],
                    },
                ],
            },
        ]
        "###);
        let double_quoted_ast = ast_of_string(r#"" U S A ""#, Rule::string_literal)?;
        assert_yaml_snapshot!(double_quoted_ast, @r###"
        ---
        String: " U S A "
        "###);

        let single_quoted_ast = ast_of_string(r#"' U S A '"#, Rule::string_literal)?;
        assert_eq!(single_quoted_ast, double_quoted_ast);

        // Single quotes within double quotes should produce a string containing
        // the single quotes (and vice versa).
        assert_yaml_snapshot!( ast_of_string(r#""' U S A '""#, Rule::string_literal)? , @r###"
        ---
        String: "' U S A '"
        "###);
        assert_yaml_snapshot!( ast_of_string(r#"'" U S A "'"#, Rule::string_literal)? , @r###"
        ---
        String: "\" U S A \""
        "###);

        assert!(ast_of_string(r#"" U S A"#, Rule::string_literal).is_err());
        assert!(ast_of_string(r#"" U S A '"#, Rule::string_literal).is_err());

        Ok(())
    }

    #[test]
    fn test_parse_s_string() -> Result<()> {
        assert_debug_snapshot!(parse_tree_of_str(r#"s"SUM({col})""#, Rule::s_string)?);
        assert_yaml_snapshot!(ast_of_string(r#"s"SUM({col})""#, Rule::s_string)?, @r###"
        ---
        SString:
          - String: SUM(
          - Expr:
              Ident: col
          - String: )
        "###);
        assert_yaml_snapshot!(ast_of_string(r#"s"SUM({2 + 2})""#, Rule::s_string)?, @r###"
        ---
        SString:
          - String: SUM(
          - Expr:
              Expr:
                - Raw: "2"
                - Raw: +
                - Raw: "2"
          - String: )
        "###);
        Ok(())
    }

    #[test]
    fn test_parse_list() -> Result<()> {
        assert_debug_snapshot!(parse_tree_of_str(r#"[1 + 1, 2]"#, Rule::list)?);
        assert_yaml_snapshot!(ast_of_string(r#"[1 + 1, 2]"#, Rule::list)?, @r###"
        ---
        List:
          - alias: ~
            expr:
              Expr:
                - Raw: "1"
                - Raw: +
                - Raw: "1"
          - alias: ~
            expr:
              Raw: "2"
        "###);
        assert_yaml_snapshot!(ast_of_string(r#"[1 + f 1, 2]"#, Rule::list)?, @r###"
        ---
        List:
          - alias: ~
            expr:
              Expr:
                - Raw: "1"
                - Raw: +
                - FuncCall:
                    name: f
                    args:
                      - Raw: "1"
                    named_args: []
          - alias: ~
            expr:
              Raw: "2"
        "###);
        let ab = ast_of_string(r#"[a b]"#, Rule::list)?;
        let a_comma_b = ast_of_string(r#"[a, b]"#, Rule::list)?;
        assert_yaml_snapshot!(ab, @r###"
        ---
        List:
          - alias: ~
            expr:
              FuncCall:
                name: a
                args:
                  - Ident: b
                named_args: []
        "###);
        assert_yaml_snapshot!(a_comma_b, @r###"
        ---
        List:
          - alias: ~
            expr:
              Ident: a
          - alias: ~
            expr:
              Ident: b
        "###);
        assert_ne!(ab, a_comma_b);
        Ok(())
    }

    #[test]
    fn test_parse_number() -> Result<()> {
        assert_debug_snapshot!(parse_tree_of_str(r#"23"#, Rule::number)?, @r###"
        [
            Pair {
                rule: number,
                span: Span {
                    str: "23",
                    start: 0,
                    end: 2,
                },
                inner: [],
            },
        ]
        "###);
        assert_debug_snapshot!(parse_tree_of_str(r#"2 + 2"#, Rule::expr)?);
        Ok(())
    }

    #[test]
    fn test_parse_filter() -> Result<()> {
        assert_yaml_snapshot!(
            ast_of_string(r#"filter country = "USA""#, Rule::transformation)?
        , @r###"
        ---
        Transformation:
          Filter:
            - Expr:
                - Ident: country
                - Raw: "="
                - String: USA
        "###);
        // TODO: Shoud the next two be different, based on whether there are
        // parentheses? I think possibly not.
        assert_yaml_snapshot!(
            ast_of_string(r#"filter (upper country) = "USA""#, Rule::transformation)?
        , @r###"
        ---
        Transformation:
          Filter:
            - Expr:
                - FuncCall:
                    name: upper
                    args:
                      - Ident: country
                    named_args: []
                - Raw: "="
                - String: USA
        "###);

        let res = ast_of_string(r#"filter upper country = "USA""#, Rule::transformation);
        assert!(res.is_err());

        Ok(())
    }

    #[test]
    fn test_parse_aggregate() -> Result<()> {
        let aggregate = ast_of_string(
            "aggregate by:[title] [sum salary, count]",
            Rule::transformation,
        )?;
        assert_yaml_snapshot!(
            aggregate, @r###"
        ---
        Transformation:
          Aggregate:
            by:
              - Ident: title
            select:
              - alias: ~
                expr:
                  FuncCall:
                    name: sum
                    args:
                      - Ident: salary
                    named_args: []
              - alias: ~
                expr:
                  Ident: count
        "###);
        let aggregate = ast_of_string("aggregate by:[title] [sum salary]", Rule::transformation)?;
        assert_yaml_snapshot!(
            aggregate, @r###"
        ---
        Transformation:
          Aggregate:
            by:
              - Ident: title
            select:
              - alias: ~
                expr:
                  FuncCall:
                    name: sum
                    args:
                      - Ident: salary
                    named_args: []
        "###);

        let item = ast_of_string("aggregate by:[title] [sum salary]", Rule::transformation)?;
        let aggregate = item
            .as_transformation()
            .ok_or_else(|| anyhow!("Expected Raw"))?;
        assert!(if let Transformation::Aggregate { by, .. } = aggregate {
            by.len() == 1 && by[0].as_ident().ok_or_else(|| anyhow!("Expected Ident"))? == "title"
        } else {
            false
        });

        assert_yaml_snapshot!(
            ast_of_string("aggregate by:[title] [sum salary]", Rule::transformation)?, @r###"
        ---
        Transformation:
          Aggregate:
            by:
              - Ident: title
            select:
              - alias: ~
                expr:
                  FuncCall:
                    name: sum
                    args:
                      - Ident: salary
                    named_args: []
        "###);
        Ok(())
    }

    #[test]
    fn test_parse_select() -> Result<()> {
        assert_yaml_snapshot!(
            ast_of_string(r#"select x"#, Rule::transformation)?
        , @r###"
        ---
        Transformation:
          Select:
            - alias: ~
              expr:
                Ident: x
        "###);

        assert_yaml_snapshot!(
            ast_of_string(r#"select [x, y]"#, Rule::transformation)?
        , @r###"
        ---
        Transformation:
          Select:
            - alias: ~
              expr:
                Ident: x
            - alias: ~
              expr:
                Ident: y
        "###);

        Ok(())
    }

    #[test]
    fn test_parse_expr() -> Result<()> {
        assert_yaml_snapshot!(
            ast_of_string(r#"country = "USA""#, Rule::expr)?
        , @r###"
        ---
        Expr:
          - Ident: country
          - Raw: "="
          - String: USA
        "###);
        assert_yaml_snapshot!(ast_of_string(
                r#"[
  gross_salary ~ salary + payroll_tax,
  gross_cost   ~ gross_salary + benefits_cost,
]"#,
        Rule::list)?, @r###"
        ---
        List:
          - alias: gross_salary
            expr:
              Expr:
                - Ident: salary
                - Raw: +
                - Ident: payroll_tax
          - alias: gross_cost
            expr:
              Expr:
                - Ident: gross_salary
                - Raw: +
                - Ident: benefits_cost
        "###);
        assert_yaml_snapshot!(
            ast_of_string(
                "gross_salary ~ (salary + payroll_tax) * (1 + tax_rate)",
                Rule::named_expr,
            )?,
            @r###"
        ---
        NamedExpr:
          alias: gross_salary
          expr:
            Expr:
              - Expr:
                  - Ident: salary
                  - Raw: +
                  - Ident: payroll_tax
              - Raw: "*"
              - Expr:
                  - Raw: "1"
                  - Raw: +
                  - Ident: tax_rate
        "###);
        Ok(())
    }

    #[test]
    fn test_parse_query() -> Result<()> {
        assert_yaml_snapshot!(ast_of_string(
            r#"
from employees
filter country = "USA"                        # Each line transforms the previous result.
derive [                                      # This adds columns / variables.
  gross_salary ~ salary + payroll_tax,
  gross_cost ~   gross_salary + benefits_cost # Variables can use other variables.
]
filter gross_cost > 0
aggregate by:[title, country] [               # `by` are the columns to group by.
                   average salary,            # These are aggregation calcs run on each group.
                   sum salary,
                   average gross_salary,
                   sum gross_salary,
                   average gross_cost,
  sum_gross_cost ~ sum gross_cost,
  ct             ~ count,
]
sort sum_gross_cost
filter ct > 200
take 20
    "#
            .trim(),
            Rule::query,
        )?);
        Ok(())
    }

    #[test]
    fn test_parse_function() -> Result<()> {
        assert_debug_snapshot!(parse_tree_of_str(
            "func plus_one x = x + 1",
            Rule::func_def
        )?);
        assert_yaml_snapshot!(ast_of_string(
            "func identity x = x", Rule::func_def
        )?
        , @r###"
        ---
        FuncDef:
          name: identity
          positional_params:
            - x
          named_params: []
          body:
            Ident: x
        "###);
        assert_yaml_snapshot!(ast_of_string(
            "func plus_one x = (x + 1)", Rule::func_def
        )?
        , @r###"
        ---
        FuncDef:
          name: plus_one
          positional_params:
            - x
          named_params: []
          body:
            Expr:
              - Ident: x
              - Raw: +
              - Raw: "1"
        "###);
        assert_yaml_snapshot!(ast_of_string(
            "func plus_one x = x + 1", Rule::func_def
        )?
        , @r###"
        ---
        FuncDef:
          name: plus_one
          positional_params:
            - x
          named_params: []
          body:
            Expr:
              - Ident: x
              - Raw: +
              - Raw: "1"
        "###);
        // An example to show that we can't delayer the tree, despite there
        // being lots of layers.
        assert_yaml_snapshot!(ast_of_string(
            "func foo x = (foo bar + 1) (plax) - baz", Rule::func_def
        )?
        , @r###"
        ---
        FuncDef:
          name: foo
          positional_params:
            - x
          named_params: []
          body:
            Expr:
              - FuncCall:
                  name: foo
                  args:
                    - Ident: bar
                  named_args: []
              - Raw: +
              - Raw: "1"
        "###);

        assert_yaml_snapshot!(ast_of_string("func return_constant = 42", Rule::func_def)?, @r###"
        ---
        FuncDef:
          name: return_constant
          positional_params: []
          named_params: []
          body:
            Raw: "42"
        "###);
        assert_yaml_snapshot!(ast_of_string(r#"func count X = s"SUM({X})""#, Rule::func_def)?, @r###"
        ---
        FuncDef:
          name: count
          positional_params:
            - X
          named_params: []
          body:
            SString:
              - String: SUM(
              - Expr:
                  Ident: X
              - String: )
        "###);

        /* TODO: Does not yet parse because `window` not yet implemented.
            assert_debug_snapshot!(ast_of_parse_tree(
                parse_tree_of_str(
                    r#"
        func lag_day x = (
          window x
          by sec_id
          sort date
          lag 1
        )
                    "#,
                    Rule::func_def
                )
                .unwrap()
            ));
            */

        assert_yaml_snapshot!(ast_of_string(r#"func add x to:a = x + to"#, Rule::func_def)?, @r###"
        ---
        FuncDef:
          name: add
          positional_params:
            - x
          named_params:
            - name: to
              arg:
                Ident: a
          body:
            Expr:
              - Ident: x
              - Raw: +
              - Ident: to
        "###);

        Ok(())
    }

    #[test]
    fn test_parse_func_call() -> Result<()> {
        // Uber-hack from #154
        let ast = ast_of_string(r#"count *"#, Rule::expr)?;
        let func_call: FuncCall = ast.into_func_call()?;
        assert_yaml_snapshot!(
            func_call, @r###"
        ---
        name: count
        args:
          - Raw: "*"
        named_args: []
        "###);

        // A non-friendly option for #154
        let ast = ast_of_string(r#"count s'*'"#, Rule::expr)?;
        let func_call: FuncCall = ast.into_func_call()?;
        assert_yaml_snapshot!(
            func_call, @r###"
        ---
        name: count
        args:
          - SString:
              - String: "*"
        named_args: []
        "###);

        Ok(())
    }

    #[test]
    fn test_parse_table() -> Result<()> {
        assert_yaml_snapshot!(ast_of_string(
            "table newest_employees = ( from employees )",
            Rule::table
        )?, @r###"
        ---
        Table:
          name: newest_employees
          pipeline:
            - From:
                name: employees
                alias: ~
        "###);

        assert_yaml_snapshot!(ast_of_string(
            r#"
        table newest_employees = (
          from employees
          aggregate by:country [
            average_country_salary ~ average salary
          ]
          sort tenure
          take 50
        )"#.trim(), Rule::table)?,
         @r###"
        ---
        Table:
          name: newest_employees
          pipeline:
            - From:
                name: employees
                alias: ~
            - Aggregate:
                by:
                  - Ident: country
                select:
                  - alias: average_country_salary
                    expr:
                      FuncCall:
                        name: average
                        args:
                          - Ident: salary
                        named_args: []
            - Sort:
                - Ident: tenure
            - Take: 50
        "###);
        Ok(())
    }

    #[test]
    fn test_parse_into_parse_tree() -> Result<()> {
        assert_debug_snapshot!(parse_tree_of_str(r#"country = "USA""#, Rule::expr)?);
        assert_debug_snapshot!(parse_tree_of_str("select [a, b, c]", Rule::transformation)?);
        assert_debug_snapshot!(parse_tree_of_str(
            "aggregate by:[title, country] [sum salary]",
            Rule::transformation
        )?);
        assert_debug_snapshot!(parse_tree_of_str(
            r#"    filter country = "USA""#,
            Rule::transformation
        )?);
        assert_debug_snapshot!(parse_tree_of_str("[a, b, c,]", Rule::list)?);
        assert_debug_snapshot!(parse_tree_of_str(
            r#"[
  gross_salary ~ salary + payroll_tax,
  gross_cost   ~ gross_salary + benefits_cost
]"#,
            Rule::list
        )?);
        // Currently not putting comments in our parse tree, so this is blank.
        assert_debug_snapshot!(parse_tree_of_str(
            r#"# this is a comment
        select a"#,
            Rule::COMMENT
        )?);
        assert_debug_snapshot!(parse_tree_of_str(
            "join country [id=employee_id]",
            Rule::transformation
        )?);
        assert_debug_snapshot!(parse_tree_of_str(
            "join side:left country [id=employee_id]",
            Rule::transformation
        )?);
        assert_debug_snapshot!(parse_tree_of_str("1  + 2", Rule::expr)?);
        Ok(())
    }

    #[test]
    fn test_inline_pipeline() -> Result<()> {
        assert_debug_snapshot!(parse_tree_of_str(
            "(salary | percentile 50)",
            Rule::inline_pipeline
        )?);
        assert_yaml_snapshot!(ast_of_string("(salary | percentile 50)", Rule::inline_pipeline)?, @r###"
        ---
        InlinePipeline:
          value:
            Ident: salary
          functions:
            - name: percentile
              args:
                - Raw: "50"
              named_args: []
        "###);
        assert_yaml_snapshot!(ast_of_string("func median x = (x | percentile 50)", Rule::query)?, @r###"
        ---
        Query:
          items:
            - FuncDef:
                name: median
                positional_params:
                  - x
                named_params: []
                body:
                  InlinePipeline:
                    value:
                      Ident: x
                    functions:
                      - name: percentile
                        args:
                          - Raw: "50"
                        named_args: []
        "###);

        Ok(())
    }

    #[test]
    fn test_parse_pipeline_parse_tree() -> Result<()> {
        assert_debug_snapshot!(parse_tree_of_str(
            r#"
    from employees
    select [a, b]
    "#
            .trim(),
            Rule::pipeline
        )?);
        assert_debug_snapshot!(parse_tree_of_str(
            r#"
    from employees
    filter country = "USA"
    "#
            .trim(),
            Rule::pipeline
        )?);
        assert_debug_snapshot!(parse_tree_of_str(
            r#"
from employees
filter country = "USA"                           # Each line transforms the previous result.
derive [                                         # This adds columns / variables.
  gross_salary ~ salary + payroll_tax,
  gross_cost   ~ gross_salary + benefits_cost    # Variables can use other variables.
]
filter gross_cost > 0
aggregate by:[title, country] [                  # `by` are the columns to group by.
    average salary,                              # These are aggregation calcs run on each group.
    sum     salary,
    average gross_salary,
    sum     gross_salary,
    average gross_cost,
    sum_gross_cost ~ sum gross_cost,
    count ~ count *,
]
sort sum_gross_cost
filter count > 200
take 20
    "#
            .trim(),
            Rule::pipeline
        )?);
        Ok(())
    }
}
