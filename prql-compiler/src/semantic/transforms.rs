use anyhow::{anyhow, bail, Result};
use itertools::Itertools;

use crate::ast::ast_fold::*;
use crate::ast::*;
use crate::error::{Error, Reason};

use super::frame::extract_sorts;
use super::Context;

pub fn construct_transforms(nodes: Vec<Node>, context: Context) -> Result<(Vec<Node>, Context)> {
    let mut resolver = TransformConstructor::new(context);

    let nodes = resolver.fold_nodes(nodes)?;

    Ok((nodes, resolver.context))
}

/// Can fold (walk) over AST and replaces some [FuncCall]s with [Transform]s
pub struct TransformConstructor {
    context: Context,

    within_group: Vec<usize>,

    within_window: Option<(WindowKind, Range)>,

    within_aggregate: bool,

    sorted: Vec<ColumnSort<usize>>,
}

impl TransformConstructor {
    fn new(context: Context) -> Self {
        TransformConstructor {
            context,
            within_group: vec![],
            within_window: None,
            within_aggregate: false,
            sorted: vec![],
        }
    }
}

impl AstFold for TransformConstructor {
    fn fold_node(&mut self, mut node: Node) -> Result<Node> {
        match node.item {
            Item::FuncCall(func_call) => {
                if let Some(transform) = cast_transform(&func_call, node.declared_at)? {
                    node.item = Item::Transform(self.fold_transform(transform)?);
                } else {
                    let func_def = self.context.declarations.get_func(node.declared_at)?;
                    let return_type = func_def.return_ty.clone();

                    let func_call = Item::FuncCall(self.fold_func_call(func_call)?);

                    // wrap into windowed
                    if Some(Ty::column()) <= return_type && !self.within_aggregate {
                        node.item = self.wrap_into_windowed(func_call, node.declared_at);
                        node.declared_at = None;
                    } else {
                        node.item = func_call;
                    }
                }
            }

            item => {
                node.item = fold_item(self, item)?;
            }
        }
        Ok(node)
    }

    fn fold_transform(&mut self, t: Transform) -> Result<Transform> {
        let mut t = match t {
            Transform::From(t) => {
                self.sorted.clear();

                Transform::From(t)
            }

            Transform::Select(assigns) => Transform::Select(self.fold_nodes(assigns)?),
            Transform::Derive(assigns) => Transform::Derive(self.fold_nodes(assigns)?),
            Transform::Group { by, pipeline } => {
                let by = self.fold_nodes(by)?;

                self.within_group = by.iter().filter_map(|n| n.declared_at).collect();
                self.sorted.clear();

                let pipeline = Box::new(self.fold_node(*pipeline)?);

                self.within_group.clear();
                self.sorted.clear();

                Transform::Group { by, pipeline }
            }
            Transform::Aggregate { assigns, by } => {
                self.within_aggregate = true;
                let assigns = self.fold_nodes(assigns)?;
                self.within_aggregate = false;

                Transform::Aggregate { assigns, by }
            }
            Transform::Join { side, with, filter } => Transform::Join {
                side,
                with,
                filter: self.fold_join_filter(filter)?,
            },
            Transform::Sort(sorts) => {
                let sorts = self.fold_column_sorts(sorts)?;

                self.sorted = extract_sorts(&sorts)?;

                Transform::Sort(sorts)
            }
            Transform::Window {
                range,
                kind,
                pipeline,
            } => {
                self.within_window = Some((kind.clone(), range.clone()));
                let pipeline = Box::new(self.fold_node(*pipeline)?);
                self.within_window = None;

                Transform::Window {
                    range,
                    kind,
                    pipeline,
                }
            }

            t => fold_transform(self, t)?,
        };

        if !self.within_group.is_empty() {
            self.apply_group(&mut t)?;
        }
        if self.within_window.is_some() {
            self.apply_window(&mut t)?;
        }

        Ok(t)
    }
}

impl TransformConstructor {
    fn wrap_into_windowed(&self, expr: Item, declared_at: Option<usize>) -> Item {
        const REF: &str = "<ref>";

        let mut expr: Node = expr.into();
        expr.declared_at = declared_at;

        let frame = self
            .within_window
            .clone()
            .unwrap_or((WindowKind::Rows, Range::unbounded()));

        let mut window = Windowed::new(expr, frame);

        if !self.within_group.is_empty() {
            window.group = (self.within_group)
                .iter()
                .map(|id| Node::new_ident(REF, *id))
                .collect();
        }
        if !self.sorted.is_empty() {
            window.sort = (self.sorted)
                .iter()
                .map(|s| ColumnSort {
                    column: Node::new_ident(REF, s.column),
                    direction: s.direction.clone(),
                })
                .collect();
        }

        Item::Windowed(window)
    }

    fn apply_group(&mut self, t: &mut Transform) -> Result<()> {
        match t {
            Transform::Select(_)
            | Transform::Derive(_)
            | Transform::Sort(_)
            | Transform::Window { .. } => {
                // ok
            }
            Transform::Aggregate { by, .. } => {
                *by = (self.within_group)
                    .iter()
                    .map(|id| Node::new_ident("<ref>", *id))
                    .collect();
            }
            Transform::Take { by, sort, .. } => {
                *by = (self.within_group)
                    .iter()
                    .map(|id| Node::new_ident("<ref>", *id))
                    .collect();

                *sort = (self.sorted)
                    .iter()
                    .map(|s| ColumnSort {
                        column: Node::new_ident("<ref>", s.column),
                        direction: s.direction.clone(),
                    })
                    .collect();
            }
            _ => {
                // TODO: attach span to this error
                bail!(Error::new(Reason::Simple(format!(
                    "transform `{}` is not allowed within group context",
                    t.as_ref()
                ))))
            }
        }
        Ok(())
    }

    fn apply_window(&mut self, t: &mut Transform) -> Result<()> {
        if !matches!(t, Transform::Select(_) | Transform::Derive(_)) {
            // TODO: attach span to this error
            bail!(Error::new(Reason::Simple(format!(
                "transform `{}` is not allowed within window context",
                t.as_ref()
            ))))
        }
        Ok(())
    }
}

pub fn cast_transform(func_call: &FuncCall, id: Option<usize>) -> Result<Option<Transform>> {
    Ok(Some(match id {
        Some(1) => {
            let ([with], []) = unpack(func_call, [])?;

            Transform::From(unpack_table_ref(with))
        }
        Some(4) => {
            let ([assigns], []) = unpack(func_call, [])?;

            Transform::Select(assigns.item.into_list().unwrap())
        }
        Some(7) => {
            let ([filter], []) = unpack(func_call, [])?;

            Transform::Filter(Box::new(filter))
        }
        Some(10) => {
            let ([assigns], []) = unpack(func_call, [])?;

            Transform::Derive(assigns.item.into_list().unwrap())
        }
        Some(13) => {
            let ([assigns], []) = unpack(func_call, [])?;

            Transform::Aggregate {
                assigns: assigns.item.into_list().unwrap(),
                by: vec![],
            }
        }
        Some(16) => {
            let ([by], []) = unpack(func_call, [])?;

            let by = by
                .coerce_to_vec()
                .into_iter()
                .map(|node| {
                    let (column, direction) = match &node.item {
                        Item::Ident(_) => (node.clone(), SortDirection::default()),
                        Item::Unary { op, expr: a }
                            if matches!((op, &a.item), (UnOp::Neg, Item::Ident(_))) =>
                        {
                            (*a.clone(), SortDirection::Desc)
                        }
                        _ => {
                            return Err(Error::new(Reason::Expected {
                                who: Some("`sort`".to_string()),
                                expected: "column name, optionally prefixed with + or -"
                                    .to_string(),
                                found: node.item.to_string(),
                            })
                            .with_span(node.span));
                        }
                    };

                    if matches!(column.item, Item::Ident(_)) {
                        Ok(ColumnSort { direction, column })
                    } else {
                        Err(Error::new(Reason::Expected {
                            who: Some("`sort`".to_string()),
                            expected: "column name".to_string(),
                            found: format!("`{}`", column.item),
                        })
                        .with_help("you can introduce a new column with `derive`")
                        .with_span(column.span))
                    }
                })
                .try_collect()?;

            Transform::Sort(by)
        }
        Some(19) => {
            let ([expr], []) = unpack(func_call, [])?;

            let range = match expr.discard_name()?.item {
                Item::Literal(Literal::Integer(n)) => Range::from_ints(None, Some(n)),
                Item::Range(range) => range,
                _ => unimplemented!(),
            };
            Transform::Take {
                range,
                by: vec![],
                sort: vec![],
            }
        }
        Some(24) => {
            let ([with, filter], [side]) = unpack(func_call, ["side"])?;

            let side = if let Some(side) = side {
                let span = side.span;
                let ident = side.unwrap(Item::into_ident, "ident")?;
                match ident.as_str() {
                    "inner" => JoinSide::Inner,
                    "left" => JoinSide::Left,
                    "right" => JoinSide::Right,
                    "full" => JoinSide::Full,

                    found => bail!(Error::new(Reason::Expected {
                        who: Some("`side`".to_string()),
                        expected: "inner, left, right or full".to_string(),
                        found: found.to_string()
                    })
                    .with_span(span)),
                }
            } else {
                JoinSide::Inner
            };

            let with = unpack_table_ref(with);

            let filter = filter.discard_name()?.coerce_to_vec();
            let use_using = (filter.iter().map(|x| &x.item)).all(|x| matches!(x, Item::Ident(_)));

            let filter = if use_using {
                JoinFilter::Using(filter)
            } else {
                JoinFilter::On(filter)
            };

            Transform::Join { side, with, filter }
        }
        Some(28) => {
            let ([by, pipeline], []) = unpack(func_call, [])?;

            let by = by
                .coerce_to_vec()
                .into_iter()
                // check that they are only idents
                .map(|n| match n.item {
                    Item::Ident(_) => Ok(n),
                    _ => Err(Error::new(Reason::Simple(
                        "`group` expects only idents for the `by` argument".to_string(),
                    ))
                    .with_span(n.span)),
                })
                .try_collect()?;

            let pipeline = Box::new(Item::Pipeline(pipeline.coerce_to_pipeline()).into());

            Transform::Group { by, pipeline }
        }
        Some(35) => {
            let ([pipeline], [rows, range, expanding, rolling]) =
                unpack(func_call, ["rows", "range", "expanding", "rolling"])?;

            let expanding = if let Some(expanding) = expanding {
                let as_bool = expanding.item.as_literal().and_then(|l| l.as_boolean());

                *as_bool.ok_or_else(|| {
                    Error::new(Reason::Expected {
                        who: Some("parameter `expanding`".to_string()),
                        expected: "a boolean".to_string(),
                        found: format!("{}", expanding.item),
                    })
                    .with_span(expanding.span)
                })?
            } else {
                false
            };

            let rolling = if let Some(rolling) = rolling {
                let as_int = rolling.item.as_literal().and_then(|x| x.as_integer());

                *as_int.ok_or_else(|| {
                    Error::new(Reason::Expected {
                        who: Some("parameter `rolling`".to_string()),
                        expected: "a number".to_string(),
                        found: format!("{}", rolling.item),
                    })
                    .with_span(rolling.span)
                })?
            } else {
                0
            };

            let rows = if let Some(rows) = rows {
                Some(rows.item.into_range().map_err(|x| {
                    Error::new(Reason::Expected {
                        who: Some("parameter `rows`".to_string()),
                        expected: "a range".to_string(),
                        found: format!("{}", x),
                    })
                    .with_span(rows.span)
                })?)
            } else {
                None
            };

            let range = if let Some(range) = range {
                Some(range.item.into_range().map_err(|x| {
                    Error::new(Reason::Expected {
                        who: Some("parameter `range`".to_string()),
                        expected: "a range".to_string(),
                        found: format!("{}", x),
                    })
                    .with_span(range.span)
                })?)
            } else {
                None
            };

            let (kind, range) = if expanding {
                (WindowKind::Rows, Range::from_ints(None, Some(0)))
            } else if rolling > 0 {
                (
                    WindowKind::Rows,
                    Range::from_ints(Some(-rolling + 1), Some(0)),
                )
            } else if let Some(range) = rows {
                (WindowKind::Rows, range)
            } else if let Some(range) = range {
                (WindowKind::Range, range)
            } else {
                (WindowKind::Rows, Range::unbounded())
            };
            Transform::Window {
                range,
                kind,
                pipeline: Box::new(Item::Pipeline(pipeline.coerce_to_pipeline()).into()),
            }
        }
        _ => return Ok(None),
    }))
}

fn unpack_table_ref(node: Node) -> TableRef {
    let declared_at = node.declared_at;
    let (alias, expr) = node.into_name_and_expr();

    let name = expr.item.into_ident().unwrap();
    TableRef {
        name,
        alias,
        declared_at,
    }
}

fn unpack<const P: usize, const N: usize>(
    func_call: &FuncCall,
    expected: [&str; N],
) -> Result<([Node; P], [Option<Node>; N])> {
    let mut func_call = func_call.clone();

    // named
    const NONE: Option<Node> = None;
    let mut named = [NONE; N];

    for (i, e) in expected.into_iter().enumerate() {
        if let Some(val) = func_call.named_args.remove(e) {
            named[i] = Some(*val);
        }
    }

    // positional
    let positional =
        (func_call.args.try_into()).map_err(|_| anyhow!("bad `{}` definition", func_call.name))?;

    Ok((positional, named))
}

#[cfg(test)]
mod tests {
    use insta::assert_yaml_snapshot;

    use crate::sql::load_std_lib;
    use crate::{analyze, parse};

    #[test]
    fn test_aggregate_positional_arg() {
        let stdlib = load_std_lib().unwrap();
        let (_, context) = analyze(stdlib, None).unwrap();
        let context = Some(context);

        // distinct query #292
        let query = parse(
            "
        from c_invoice
        select invoice_no
        group invoice_no (
            take 1
        )
        ",
        )
        .unwrap();
        let (result, _) = analyze(query.nodes, context.clone()).unwrap();
        assert_yaml_snapshot!(result, @r###"
        ---
        - Pipeline:
            nodes:
              - Transform:
                  From:
                    name: c_invoice
                    alias: ~
                    declared_at: 79
                ty:
                  Literal: Table
              - Transform:
                  Select:
                    - Ident: invoice_no
                      ty:
                        Literal: Column
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
                      - Ident: invoice_no
                        ty:
                          Literal: Column
                    pipeline:
                      Pipeline:
                        nodes:
                          - Transform:
                              Take:
                                range:
                                  start: ~
                                  end:
                                    Literal:
                                      Integer: 1
                                by:
                                  - Ident: "<ref>"
                                sort: []
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
          ty:
            Literal: Table
        "###);

        // oops, two arguments #339
        let query = parse(
            "
        from c_invoice
        aggregate average amount
        ",
        )
        .unwrap();
        let result = analyze(query.nodes, context.clone());
        assert!(result.is_err());

        // oops, two arguments
        let query = parse(
            "
        from c_invoice
        group date (aggregate average amount)
        ",
        )
        .unwrap();
        let result = analyze(query.nodes, context.clone());
        assert!(result.is_err());

        // correct function call
        let query = parse(
            "
        from c_invoice
        group date (
            aggregate (average amount)
        )
        ",
        )
        .unwrap();
        let (result, _) = analyze(query.nodes, context).unwrap();
        assert_yaml_snapshot!(result, @r###"
        ---
        - Pipeline:
            nodes:
              - Transform:
                  From:
                    name: c_invoice
                    alias: ~
                    declared_at: 79
              - Transform:
                  Group:
                    by:
                      - Ident: date
                        ty:
                          Literal: Column
                    pipeline:
                      Pipeline:
                        nodes:
                          - Transform:
                              Aggregate:
                                assigns:
                                  - Ident: "<unnamed>"
                                    ty:
                                      AnyOf:
                                        - Literal: Scalar
                                        - Literal: Column
                                by:
                                  - Ident: "<ref>"
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
          ty:
            Literal: Table
        "###);
    }

    #[test]
    fn test_transform_sort() {
        let stdlib = load_std_lib().unwrap();
        let (_, context) = analyze(stdlib, None).unwrap();
        let context = Some(context);

        let query = parse(
            "
        from invoices
        sort [issued_at, -amount, +num_of_articles]
        sort issued_at
        sort (-issued_at)
        sort [issued_at]
        sort [-issued_at]
        ",
        )
        .unwrap();

        let (result, _) = analyze(query.nodes, context).unwrap();
        assert_yaml_snapshot!(result, @r###"
        ---
        - Pipeline:
            nodes:
              - Transform:
                  From:
                    name: invoices
                    alias: ~
                    declared_at: 79
                ty:
                  Literal: Table
              - Transform:
                  Sort:
                    - direction: Asc
                      column:
                        Ident: issued_at
                        ty:
                          Literal: Column
                    - direction: Desc
                      column:
                        Ident: amount
                        ty:
                          Literal: Column
                    - direction: Asc
                      column:
                        Ident: num_of_articles
                        ty:
                          Literal: Column
                ty:
                  Function:
                    named: {}
                    args:
                      - Infer
                    return_ty:
                      Literal: Table
              - Transform:
                  Sort:
                    - direction: Asc
                      column:
                        Ident: issued_at
                        ty:
                          Literal: Column
                ty:
                  Function:
                    named: {}
                    args:
                      - Infer
                    return_ty:
                      Literal: Table
              - Transform:
                  Sort:
                    - direction: Desc
                      column:
                        Ident: issued_at
                        ty:
                          Literal: Column
                ty:
                  Function:
                    named: {}
                    args:
                      - Infer
                    return_ty:
                      Literal: Table
              - Transform:
                  Sort:
                    - direction: Asc
                      column:
                        Ident: issued_at
                        ty:
                          Literal: Column
                ty:
                  Function:
                    named: {}
                    args:
                      - Infer
                    return_ty:
                      Literal: Table
              - Transform:
                  Sort:
                    - direction: Desc
                      column:
                        Ident: issued_at
                        ty:
                          Literal: Column
                ty:
                  Function:
                    named: {}
                    args:
                      - Infer
                    return_ty:
                      Literal: Table
          ty:
            Literal: Table
        "###);
    }
}
