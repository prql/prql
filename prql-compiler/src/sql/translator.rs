//! This module is responsible for translating PRQL AST to sqlparser AST, and
//! then to a String. We use sqlparser because it's trivial to create the string
//! once it's in their AST (it's just `.to_string()`). It also lets us support a
//! few dialects of SQL immediately.
// The average code quality here is low — we're basically plugging in test
// cases and fixing what breaks, with some occasional refactors. I'm not sure
// that's a terrible approach — the SQL spec is huge, so we're not reasonably
// going to be isomorphically mapping everything back from SQL to PRQL. But it
// does mean we should continue to iterate on this file and refactor things when
// necessary.
use anyhow::{anyhow, bail, Result};
use itertools::Itertools;
use sqlformat::{format, FormatOptions, QueryParams};
use sqlparser::ast::{
    self as sql_ast, BinaryOperator, DateTimeField, Expr, Function, FunctionArg, FunctionArgExpr,
    Join, JoinConstraint, JoinOperator, ObjectName, OrderByExpr, Select, SelectItem, SetExpr,
    TableAlias, TableFactor, TableWithJoins, Top, UnaryOperator, Value, WindowFrameBound,
    WindowSpec,
};
use std::collections::HashMap;

use crate::ast::JoinFilter;
use crate::ast::*;
use crate::error::{Error, Reason};
use crate::semantic::Context;
use crate::utils::OrMap;

use super::materializer::MaterializationContext;
use super::{distinct, un_group, MaterializedFrame};

/// Translate a PRQL AST into a SQL string.
pub fn translate(query: Query, context: Context) -> Result<String> {
    let sql_query = translate_query(query, context)?;

    let sql_query_string = sql_query.to_string();

    let formatted = format(
        &sql_query_string,
        &QueryParams::default(),
        FormatOptions::default(),
    );

    // The sql formatter turns `{{` into `{ {`, and while that's reasonable SQL,
    // we want to allow jinja expressions through. So we (somewhat hackily) replace
    // any `{ {` with `{{`.
    let formatted = formatted.replace("{ {", "{{").replace("} }", "}}");

    Ok(formatted)
}

pub fn translate_query(query: Query, context: Context) -> Result<sql_ast::Query> {
    // extract tables and the pipeline
    let tables = into_tables(query.nodes)?;

    let mut context = MaterializationContext::from(context);

    // split to atomics
    let atomics = atomic_tables_of_tables(tables, &mut context)?;

    // materialize each atomic in two stages
    let mut materialized = Vec::new();
    for t in atomics {
        let table_id = t.name.clone().and_then(|x| x.declared_at);

        let (pipeline, frame, c) = super::materialize(t.pipeline, context, table_id)?;
        context = c;

        materialized.push(AtomicTable {
            name: t.name,
            frame: Some(frame),
            pipeline,
        });
    }

    let dialect = query.dialect.handler();

    // take last table
    if materialized.is_empty() {
        bail!("No tables?");
    }
    let main_query = materialized.remove(materialized.len() - 1);
    let ctes = materialized;

    // convert each of the CTEs
    let ctes: Vec<_> = ctes
        .into_iter()
        .map(|t| table_to_sql_cte(t, dialect.as_ref()))
        .try_collect()?;

    // convert main query
    let mut main_query = sql_query_of_atomic_table(main_query, dialect.as_ref())?;

    // attach CTEs
    if !ctes.is_empty() {
        main_query.with = Some(sql_ast::With {
            cte_tables: ctes,
            recursive: false,
        });
    }

    Ok(main_query)
}

pub struct AtomicTable {
    name: Option<TableRef>,
    pipeline: Pipeline,
    frame: Option<MaterializedFrame>,
}

fn into_tables(nodes: Vec<Node>) -> Result<Vec<Table>> {
    let mut tables: Vec<Table> = Vec::new();
    let mut transforms: Vec<Node> = Vec::new();
    for node in nodes {
        match node.item {
            Item::Table(t) => tables.push(t),
            Item::Pipeline(p) => transforms.extend(p.nodes),
            Item::Transform(_) => transforms.push(node),
            i => bail!("Unexpected item on top level: {i:?}"),
        }
    }

    Ok([tables, vec![transforms.into()]].concat())
}

fn table_to_sql_cte(table: AtomicTable, dialect: &dyn DialectHandler) -> Result<sql_ast::Cte> {
    let alias = sql_ast::TableAlias {
        name: translate_ident(table.name.clone().unwrap().name, dialect),
        columns: vec![],
    };
    Ok(sql_ast::Cte {
        alias,
        query: sql_query_of_atomic_table(table, dialect)?,
        from: None,
    })
}

fn table_factor_of_table_ref(table_ref: &TableRef, dialect: &dyn DialectHandler) -> TableFactor {
    TableFactor::Table {
        name: ObjectName(vec![translate_ident(table_ref.name.clone(), dialect)]),
        alias: table_ref.alias.clone().map(|a| TableAlias {
            name: translate_ident(a, dialect),
            columns: vec![],
        }),
        args: None,
        with_hints: vec![],
    }
}

// impl Translator for
// fn sql_query_of_atomic_table(table: AtomicTable, dialect: &Dialect) -> Result<sql_ast::Query> {
fn sql_query_of_atomic_table(
    table: AtomicTable,
    dialect: &dyn DialectHandler,
) -> Result<sql_ast::Query> {
    let frame = table.frame.ok_or_else(|| anyhow!("frame not provided?"))?;

    let transforms = table.pipeline.into_transforms()?;

    let mut from = transforms
        .iter()
        .filter_map(|t| match t {
            Transform::From(table_ref) => Some(TableWithJoins {
                relation: table_factor_of_table_ref(table_ref, dialect),
                joins: vec![],
            }),
            _ => None,
        })
        .collect::<Vec<_>>();

    let joins = transforms
        .iter()
        .filter(|t| matches!(t, Transform::Join { .. }))
        .map(|j| translate_join(j, dialect))
        .collect::<Result<Vec<_>>>()?;
    if !joins.is_empty() {
        if let Some(from) = from.last_mut() {
            from.joins = joins;
        } else {
            return Err(anyhow!("Cannot use `join` without `from`"));
        }
    }

    // Split the pipeline into before & after the aggregate
    let aggregate_position = transforms
        .iter()
        .position(|t| matches!(t, Transform::Aggregate { .. }))
        .unwrap_or(transforms.len());
    let (before, after) = transforms.split_at(aggregate_position);

    // Find the filters that come before the aggregation.
    let where_ = filter_of_pipeline(before, dialect)?;
    let having = filter_of_pipeline(after, dialect)?;

    let takes = transforms
        .iter()
        .filter_map(|t| match t {
            Transform::Take { range, .. } => Some(range.clone()),
            _ => None,
        })
        .collect();
    let take = range_of_ranges(takes)?;
    let offset = take.start.map(|s| s - 1).unwrap_or(0);
    let limit = take.end.map(|e| e - offset);

    let offset = if offset == 0 {
        None
    } else {
        Some(sqlparser::ast::Offset {
            value: translate_item(Item::Literal(Literal::Integer(offset)), dialect)?,
            rows: sqlparser::ast::OffsetRows::None,
        })
    };

    // Use sorting from the frame
    let order_by = (frame.sort)
        .into_iter()
        .map(|s| translate_column_sort(s, dialect))
        .try_collect()?;

    let aggregate = transforms.get(aggregate_position);

    let group_bys: Vec<Node> = match aggregate {
        Some(Transform::Aggregate { by, .. }) => by.clone(),
        None => vec![],
        _ => unreachable!("Expected an aggregate transformation"),
    };

    let distinct = transforms.iter().any(|t| matches!(t, Transform::Unique));

    Ok(sql_ast::Query {
        body: SetExpr::Select(Box::new(Select {
            distinct,
            top: if dialect.use_top() {
                limit.map(|l| top_of_i64(l, dialect))
            } else {
                None
            },
            projection: (frame.columns.into_iter())
                .map(|n| translate_select_item(n.item, dialect))
                .try_collect()?,
            into: None,
            from,
            lateral_views: vec![],
            selection: where_,
            group_by: try_into_exprs(group_bys, dialect)?,
            cluster_by: vec![],
            distribute_by: vec![],
            sort_by: vec![],
            having,
            qualify: None,
        })),
        order_by,
        with: None,
        limit: if dialect.use_top() {
            None
        } else {
            limit.map(expr_of_i64)
        },
        offset,
        fetch: None,
        lock: None,
    })
}

/// Convert a pipeline into a number of pipelines which can each "fit" into a SELECT.
fn atomic_pipelines_of_pipeline(
    pipeline: Pipeline,
    context: &mut MaterializationContext,
) -> Result<Vec<AtomicTable>> {
    // Insert a cut, when we find transformation that out of order:
    // - joins (no limit),
    // - filters (for WHERE)
    // - aggregate (max 1x)
    // - sort (no limit)
    // - filters (for HAVING)
    // - take (no limit)
    //
    // Select and derive should already be extracted during resolving phase.
    //
    // So we loop through the Pipeline, and cut it into cte-sized pipelines,
    // which we'll then compose together.
    let pipeline = Ok(pipeline.nodes)
        .and_then(un_group::un_group)
        .and_then(|x| distinct::take_to_distinct(x, context))?;

    let mut counts: HashMap<&str, u32> = HashMap::new();
    let mut splits = vec![0];
    for (i, function) in pipeline.iter().enumerate() {
        let transform =
            (function.item.as_transform()).ok_or_else(|| anyhow!("expected Transform"))?;

        let split = match transform.as_ref() {
            "Join" => {
                counts.get("Filter").is_some()
                    || counts.get("Aggregate").is_some()
                    || counts.get("Sort").is_some()
                    || counts.get("Take").is_some()
            }
            "Aggregate" => {
                counts.get("Aggregate").is_some()
                    || counts.get("Sort").is_some()
                    || counts.get("Take").is_some()
            }
            "Sort" => counts.get("Take").is_some(),
            "Filter" => counts.get("Take").is_some() || function.is_complex,

            // There can be many takes, but they have to be consecutive
            // For example `take 100 | sort a | take 10` can't be one CTE.
            // But this is enforced by transform order anyway.
            "Take" => false,

            _ => false,
        };

        if split {
            splits.push(i);
            counts.clear();
        }

        *counts.entry(transform.as_ref()).or_insert(0) += 1;
    }

    splits.push(pipeline.len());
    let ctes = (0..splits.len() - 1)
        .map(|i| pipeline[splits[i]..splits[i + 1]].to_vec())
        .filter(|x| !x.is_empty())
        .map(|p| p.into())
        .collect();
    Ok(ctes)
}

/// Converts a series of tables into a series of atomic tables, by putting the
/// next pipeline's `from` as the current pipelines's table name.
fn atomic_tables_of_tables(
    tables: Vec<Table>,
    context: &mut MaterializationContext,
) -> Result<Vec<AtomicTable>> {
    let mut atomics = Vec::new();
    let mut index = 0;
    for table in tables {
        // split table into atomics
        let pipeline = table.pipeline.coerce_to_pipeline();
        let mut t_atomics: Vec<_> = atomic_pipelines_of_pipeline(pipeline, context)?;

        let (last, ctes) = t_atomics
            .split_last_mut()
            .ok_or_else(|| anyhow!("No pipelines?"))?;

        // generate table names for all but last table
        let mut last_name = None;
        for cte in ctes {
            prepend_with_from(&mut cte.pipeline, last_name);

            let name = format!("table_{index}");
            let id = context.declare_table(&name);

            cte.name = Some(TableRef {
                name,
                alias: None,
                declared_at: Some(id),
            });
            index += 1;

            last_name = cte.name.clone();
        }

        // use original table name
        prepend_with_from(&mut last.pipeline, last_name);
        last.name = Some(TableRef {
            name: table.name,
            alias: None,
            declared_at: table.id,
        });

        atomics.extend(t_atomics);
    }
    Ok(atomics)
}

fn prepend_with_from(pipeline: &mut Pipeline, table: Option<TableRef>) {
    if let Some(table) = table {
        let from = Transform::From(table);
        pipeline.nodes.insert(0, Item::Transform(from).into());
    }
}

/// Aggregate several ordered ranges into one, computing the intersection.
///
/// Returns a tuple of `(start, end)`, where `end` is optional.
fn range_of_ranges(ranges: Vec<Range>) -> Result<Range<i64>> {
    let mut current = Range::default();
    for range in ranges {
        let mut range = range.into_int()?;

        // b = b + a.start -1 (take care of 1-based index!)
        range.start = range.start.or_map(current.start, |a, b| a + b - 1);
        range.end = range.end.map(|b| current.start.unwrap_or(1) + b - 1);

        // b.end = min(a.end, b.end)
        range.end = current.end.or_map(range.end, i64::min);
        current = range;
    }

    if current
        .start
        .zip(current.end)
        .map(|(s, e)| e <= s)
        .unwrap_or(false)
    {
        bail!("Range end is before its start.");
    }
    Ok(current)
}

fn filter_of_pipeline(
    pipeline: &[Transform],
    dialect: &dyn DialectHandler,
) -> Result<Option<Expr>> {
    let filters: Vec<Node> = pipeline
        .iter()
        .filter_map(|t| match t {
            Transform::Filter(filter) => Some(*filter.clone()),
            _ => None,
        })
        .collect();
    filter_of_filters(filters, dialect)
}

fn filter_of_filters(conditions: Vec<Node>, dialect: &dyn DialectHandler) -> Result<Option<Expr>> {
    let mut condition = None;
    for filter in conditions {
        if let Some(left) = condition {
            condition = Some(Node::from(Item::Binary {
                op: BinOp::And,
                left: Box::new(left),
                right: Box::new(filter),
            }))
        } else {
            condition = Some(filter)
        }
    }

    condition
        .map(|n| translate_item(n.item, dialect))
        .transpose()
}

fn expr_of_i64(number: i64) -> Expr {
    Expr::Value(Value::Number(
        number.to_string(),
        number.leading_zeros() < 32,
    ))
}

fn top_of_i64(take: i64, dialect: &dyn DialectHandler) -> Top {
    Top {
        quantity: Some(translate_item(Item::Literal(Literal::Integer(take)), dialect).unwrap()),
        with_ties: false,
        percent: false,
    }
}
fn try_into_exprs(nodes: Vec<Node>, dialect: &dyn DialectHandler) -> Result<Vec<Expr>> {
    nodes
        .into_iter()
        .map(|x| x.item)
        .map(|item| translate_item(item, dialect))
        .try_collect()
}

fn translate_select_item(item: Item, dialect: &dyn DialectHandler) -> Result<SelectItem> {
    Ok(match item {
        Item::Binary { .. }
        | Item::Unary { .. }
        | Item::SString(_)
        | Item::FString(_)
        | Item::Ident(_)
        | Item::Literal(_)
        | Item::Windowed(_) => SelectItem::UnnamedExpr(translate_item(item, dialect)?),
        Item::Assign(named) => SelectItem::ExprWithAlias {
            alias: translate_ident(named.name, dialect),
            expr: translate_item(named.expr.item, dialect)?,
        },
        _ => bail!("Can't convert to SelectItem; {:?}", item),
    })
}

fn translate_item(item: Item, dialect: &dyn DialectHandler) -> Result<Expr> {
    Ok(match item {
        Item::Ident(ident) => Expr::CompoundIdentifier(
            ident
                .split('.')
                .map(|part| translate_ident(part.to_string(), dialect))
                .collect(),
        ),

        // do we need to surround operations with parentheses?
        Item::Binary { op, left, right } => {
            if let Some(is_null) = try_into_is_null(&op, &left, &right, dialect)? {
                is_null
            } else {
                Expr::BinaryOp {
                    left: Box::new(translate_item(left.item, dialect)?),
                    op: match op {
                        BinOp::Mul => BinaryOperator::Multiply,
                        BinOp::Div => BinaryOperator::Divide,
                        BinOp::Mod => BinaryOperator::Modulo,
                        BinOp::Add => BinaryOperator::Plus,
                        BinOp::Sub => BinaryOperator::Minus,
                        BinOp::Eq => BinaryOperator::Eq,
                        BinOp::Ne => BinaryOperator::NotEq,
                        BinOp::Gt => BinaryOperator::Gt,
                        BinOp::Lt => BinaryOperator::Lt,
                        BinOp::Gte => BinaryOperator::GtEq,
                        BinOp::Lte => BinaryOperator::LtEq,
                        BinOp::And => BinaryOperator::And,
                        BinOp::Or => BinaryOperator::Or,
                        BinOp::Coalesce => unreachable!(),
                    },
                    right: Box::new(translate_item(right.item, dialect)?),
                }
            }
        }

        Item::Unary { op, expr: a } => Expr::UnaryOp {
            op: match op {
                UnOp::Neg => UnaryOperator::Minus,
                UnOp::Not => UnaryOperator::Not,
            },
            expr: Box::new(translate_item(a.item, dialect)?),
        },

        Item::Range(r) => {
            fn assert_bound(bound: Option<Box<Node>>) -> Result<Node, Error> {
                bound.map(|b| *b).ok_or_else(|| {
                    Error::new(Reason::Simple(
                        "range requires both bounds to be used this way".to_string(),
                    ))
                })
            }
            let start: Expr = translate_item(assert_bound(r.start)?.item, dialect)?;
            let end: Expr = translate_item(assert_bound(r.end)?.item, dialect)?;
            Expr::Identifier(sql_ast::Ident::new(format!("{} AND {}", start, end)))
        }
        // Fairly hacky — convert everything to a string, then concat it,
        // then convert to Expr. We can't use the `Item::Expr` code above
        // since we don't want to intersperse with spaces.
        Item::SString(s_string_items) => {
            let string = s_string_items
                .into_iter()
                .map(|s_string_item| match s_string_item {
                    InterpolateItem::String(string) => Ok(string),
                    InterpolateItem::Expr(node) => {
                        translate_item(node.item, dialect).map(|expr| expr.to_string())
                    }
                })
                .collect::<Result<Vec<String>>>()?
                .join("");
            Expr::Identifier(sql_ast::Ident::new(string))
        }
        Item::FString(f_string_items) => {
            let args = f_string_items
                .into_iter()
                .map(|item| match item {
                    InterpolateItem::String(string) => {
                        Ok(Expr::Value(Value::SingleQuotedString(string)))
                    }
                    InterpolateItem::Expr(node) => translate_item(node.item, dialect),
                })
                .map(|r| r.map(|e| FunctionArg::Unnamed(FunctionArgExpr::Expr(e))))
                .collect::<Result<Vec<_>>>()?;

            Expr::Function(Function {
                name: ObjectName(vec![sql_ast::Ident::new("CONCAT")]),
                args,
                distinct: false,
                over: None,
            })
        }
        Item::Interval(interval) => {
            let sql_parser_datetime = match interval.unit.as_str() {
                "years" => DateTimeField::Year,
                "months" => DateTimeField::Month,
                "days" => DateTimeField::Day,
                "hours" => DateTimeField::Hour,
                "minutes" => DateTimeField::Minute,
                "seconds" => DateTimeField::Second,
                _ => bail!("Unsupported interval unit: {}", interval.unit),
            };
            Expr::Value(Value::Interval {
                value: interval.n.to_string(),
                leading_field: Some(sql_parser_datetime),
                leading_precision: None,
                last_field: None,
                fractional_seconds_precision: None,
            })
        }
        Item::Windowed(window) => {
            let expr = translate_item(window.expr.item, dialect)?;

            let default_frame = if window.sort.is_empty() {
                (WindowKind::Rows, Range::unbounded())
            } else {
                (WindowKind::Range, Range::from_ints(None, Some(0)))
            };

            let window = WindowSpec {
                partition_by: try_into_exprs(window.group, dialect)?,
                order_by: (window.sort)
                    .into_iter()
                    .map(|s| translate_column_sort(s, dialect))
                    .try_collect()?,
                window_frame: if window.window == default_frame {
                    None
                } else {
                    Some(try_into_window_frame(window.window)?)
                },
            };

            Expr::Identifier(sql_ast::Ident::new(format!("{expr} OVER ({window})")))
        }
        Item::Literal(l) => match l {
            Literal::Null => Expr::Value(Value::Null),
            Literal::String(s) => Expr::Value(Value::SingleQuotedString(s)),
            Literal::Boolean(b) => Expr::Value(Value::Boolean(b)),
            Literal::Float(f) => Expr::Value(Value::Number(format!("{f}"), false)),
            Literal::Integer(i) => Expr::Value(Value::Number(format!("{i}"), false)),
            Literal::Date(value) => Expr::TypedString {
                data_type: sql_ast::DataType::Date,
                value,
            },
            Literal::Time(value) => Expr::TypedString {
                data_type: sql_ast::DataType::Time,
                value,
            },
            Literal::Timestamp(value) => Expr::TypedString {
                data_type: sql_ast::DataType::Timestamp,
                value,
            },
        },
        _ => bail!("Can't convert to Expr; {item:?}"),
    })
}
fn try_into_is_null(
    op: &BinOp,
    a: &Node,
    b: &Node,
    dialect: &dyn DialectHandler,
) -> Result<Option<Expr>> {
    if matches!(op, BinOp::Eq) || matches!(op, BinOp::Ne) {
        let expr = if matches!(a.item, Item::Literal(Literal::Null)) {
            translate_item(b.item.clone(), dialect)?
        } else if matches!(b.item, Item::Literal(Literal::Null)) {
            translate_item(a.item.clone(), dialect)?
        } else {
            return Ok(None);
        };

        return Ok(Some(if matches!(op, BinOp::Eq) {
            Expr::IsNull(Box::new(expr))
        } else {
            Expr::IsNotNull(Box::new(expr))
        }));
    }

    Ok(None)
}
fn try_into_window_frame((kind, range): (WindowKind, Range)) -> Result<sql_ast::WindowFrame> {
    fn parse_bound(bound: Node) -> Result<WindowFrameBound> {
        let as_int = bound.item.into_literal()?.into_integer()?;
        Ok(match as_int {
            0 => WindowFrameBound::CurrentRow,
            1.. => WindowFrameBound::Following(Some(as_int as u64)),
            _ => WindowFrameBound::Preceding(Some((-as_int) as u64)),
        })
    }

    Ok(sql_ast::WindowFrame {
        units: match kind {
            WindowKind::Rows => sql_ast::WindowFrameUnits::Rows,
            WindowKind::Range => sql_ast::WindowFrameUnits::Range,
        },
        start_bound: if let Some(start) = range.start {
            parse_bound(*start)?
        } else {
            WindowFrameBound::Preceding(None)
        },
        end_bound: Some(if let Some(end) = range.end {
            parse_bound(*end)?
        } else {
            WindowFrameBound::Following(None)
        }),
    })
}

// I had an idea to for stdlib functions to have "native" keyword, which would prevent them from being
// resolved and materialized and would be passed to here. But that has little advantage over current approach.
// After some time when we know that current approach is good, this impl can be removed.
#[allow(dead_code)]
fn translate_func_call(func_call: FuncCall, dialect: &dyn DialectHandler) -> Result<Function> {
    let FuncCall { name, args, .. } = func_call;

    Ok(Function {
        name: ObjectName(vec![sql_ast::Ident::new(name)]),
        args: args
            .into_iter()
            .map(|a| translate_item(a.item, dialect))
            .map(|e| e.map(|a| FunctionArg::Unnamed(FunctionArgExpr::Expr(a))))
            .collect::<Result<Vec<_>>>()?,
        over: None,
        distinct: false,
    })
}
fn translate_column_sort(sort: ColumnSort, dialect: &dyn DialectHandler) -> Result<OrderByExpr> {
    Ok(OrderByExpr {
        expr: translate_item(sort.column.item, dialect)?,
        asc: if matches!(sort.direction, SortDirection::Asc) {
            None // default order is ASC, so there is no need to emit it
        } else {
            Some(false)
        },
        nulls_first: None,
    })
}

fn translate_join(t: &Transform, dialect: &dyn DialectHandler) -> Result<Join> {
    match t {
        Transform::Join { side, with, filter } => {
            let constraint = match filter {
                JoinFilter::On(nodes) => JoinConstraint::On(
                    filter_of_filters(nodes.clone(), dialect)?
                        .unwrap_or(Expr::Value(Value::Boolean(true))),
                ),
                JoinFilter::Using(nodes) => JoinConstraint::Using(
                    nodes
                        .iter()
                        .map(|x| Ok(translate_ident(x.item.clone().into_ident()?, dialect)))
                        .collect::<Result<Vec<_>>>()?,
                ),
            };

            Ok(Join {
                relation: table_factor_of_table_ref(with, dialect),
                join_operator: match *side {
                    JoinSide::Inner => JoinOperator::Inner(constraint),
                    JoinSide::Left => JoinOperator::LeftOuter(constraint),
                    JoinSide::Right => JoinOperator::RightOuter(constraint),
                    JoinSide::Full => JoinOperator::FullOuter(constraint),
                },
            })
        }
        _ => unreachable!(),
    }
}

fn translate_ident(ident: String, dialect: &dyn DialectHandler) -> sql_ast::Ident {
    fn starting_forbidden(c: char) -> bool {
        !(('a'..='z').contains(&c) || matches!(c, '_' | '$'))
    }

    fn subsequent_forbidden(c: char) -> bool {
        !(('a'..='z').contains(&c) || ('0'..='9').contains(&c) || matches!(c, '_' | '$'))
    }

    let is_jinja = ident.starts_with("{{") && ident.ends_with("}}");
    let is_asterisk = ident == "*";

    if !is_jinja
        && !is_asterisk
        && (ident.is_empty()
            || ident.starts_with(starting_forbidden)
            || (ident.len() > 1 && ident.contains(subsequent_forbidden)))
    {
        sql_ast::Ident::with_quote(dialect.ident_quote(), ident)
    } else {
        sql_ast::Ident::new(ident)
    }
}

impl From<Vec<Node>> for Table {
    fn from(functions: Vec<Node>) -> Self {
        Table {
            id: None,
            name: String::default(),
            pipeline: Box::new(Item::Pipeline(functions.into()).into()),
        }
    }
}
impl From<Vec<Node>> for AtomicTable {
    fn from(functions: Vec<Node>) -> Self {
        AtomicTable {
            name: None,
            pipeline: functions.into(),
            frame: None,
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::{parser::parse, resolve_and_translate, resolve_names, sql::load_std_lib};
    use insta::{assert_display_snapshot, assert_snapshot, assert_yaml_snapshot};
    use serde_yaml::from_str;

    #[test]
    fn test_literal() {
        let query: Query = parse(
            r###"
        from employees
        derive [always_true = true]
        "###,
        )
        .unwrap();

        let sql = resolve_and_translate(query).unwrap();
        assert_display_snapshot!(sql,
            @r###"
        SELECT
          employees.*,
          true AS always_true
        FROM
          employees
        "###
        );
    }

    #[test]
    fn test_stdlib() {
        let query: Query = parse(
            r###"
        from employees
        aggregate (
          [salary_usd = min salary]
        )
        "###,
        )
        .unwrap();

        let sql = resolve_and_translate(query).unwrap();
        assert_snapshot!(sql,
            @r###"
        SELECT
          MIN(salary) AS salary_usd
        FROM
          employees
        "###
        );

        let query: Query = parse(
            r###"
        from employees
        aggregate (
          [salary_usd = (round salary 2)]
        )
        "###,
        )
        .unwrap();

        let sql = resolve_and_translate(query).unwrap();
        assert_snapshot!(sql,
            @r###"
        SELECT
          ROUND(salary, 2) AS salary_usd
        FROM
          employees
        "###
        );
    }

    #[test]
    fn test_range_of_ranges() -> Result<()> {
        let range1 = Range::from_ints(Some(1), Some(10));
        let range2 = Range::from_ints(Some(5), Some(6));
        let range3 = Range::from_ints(Some(5), None);
        let range4 = Range::from_ints(None, Some(8));

        assert!(range_of_ranges(vec![range1.clone()])?.end.is_some());

        assert_yaml_snapshot!(range_of_ranges(vec![range1.clone()])?, @r###"
        ---
        start: 1
        end: 10
        "###);

        assert_yaml_snapshot!(range_of_ranges(vec![range1.clone(), range1.clone()])?, @r###"
        ---
        start: 1
        end: 10
        "###);

        assert_yaml_snapshot!(range_of_ranges(vec![range1.clone(), range2.clone()])?, @r###"
        ---
        start: 5
        end: 6
        "###);

        assert_yaml_snapshot!(range_of_ranges(vec![range2.clone(), range1.clone()])?, @r###"
        ---
        start: 5
        end: 6
        "###);

        // We can't get 5..6 from 5..6.
        assert!(range_of_ranges(vec![range2.clone(), range2.clone()]).is_err());

        assert_yaml_snapshot!(range_of_ranges(vec![range3.clone(), range3.clone()])?, @r###"
        ---
        start: 9
        end: ~
        "###);

        assert_yaml_snapshot!(range_of_ranges(vec![range1, range3])?, @r###"
        ---
        start: 5
        end: 10
        "###);

        assert_yaml_snapshot!(range_of_ranges(vec![range2, range4.clone()])?, @r###"
        ---
        start: 5
        end: 6
        "###);

        assert_yaml_snapshot!(range_of_ranges(vec![range4.clone(), range4])?, @r###"
        ---
        start: ~
        end: 8
        "###);

        Ok(())
    }

    #[test]
    fn test_try_from_s_string_to_expr() -> Result<()> {
        let dialect = Dialect::Generic.handler();
        let ast: Node = from_str(
            r"
        SString:
        - String: SUM(
        - Expr:
            Ident: col
        - String: )
        ",
        )?;
        let expr: Expr = translate_item(ast.item, dialect.as_ref())?;
        assert_yaml_snapshot!(
            expr, @r###"
        ---
        Identifier:
          value: SUM(col)
          quote_style: ~
        "###
        );
        Ok(())
    }

    #[test]
    fn test_f_string() {
        let query: Query = parse(
            r###"
        from employees
        derive age = year_born - s'now()'
        select [
            f"Hello my name is {prefix}{first_name} {last_name}",
            f"and I am {age} years old."
        ]
        "###,
        )
        .unwrap();

        let sql = resolve_and_translate(query).unwrap();
        assert_display_snapshot!(sql,
            @r###"
        SELECT
          CONCAT(
            'Hello my name is ',
            prefix,
            first_name,
            ' ',
            last_name
          ),
          CONCAT('and I am ', year_born - now(), ' years old.')
        FROM
          employees
        "###
        );
    }

    fn parse_and_resolve(prql: &str) -> Result<Pipeline> {
        let std_lib = load_std_lib()?;
        let (_, context) = resolve_names(std_lib, None)?;

        let (mut nodes, _) = resolve_names(parse(prql)?.nodes, Some(context))?;
        let pipeline = nodes.remove(nodes.len() - 1).coerce_to_pipeline();
        Ok(pipeline)
    }

    #[test]
    fn test_ctes_of_pipeline() -> Result<()> {
        let mut context = MaterializationContext::default();

        // One aggregate, take at the end
        let prql: &str = r###"
        from employees
        filter country == "USA"
        aggregate [sal = average salary]
        sort sal
        take 20
        "###;

        let pipeline = parse_and_resolve(prql)?;
        let queries = atomic_pipelines_of_pipeline(pipeline, &mut context)?;
        assert_eq!(queries.len(), 1);

        // One aggregate, but take at the top
        let prql: &str = r###"
        from employees
        take 20
        filter country == "USA"
        aggregate [sal = average salary]
        sort sal
        "###;

        let pipeline = parse_and_resolve(prql)?;
        let queries = atomic_pipelines_of_pipeline(pipeline, &mut context)?;
        assert_eq!(queries.len(), 2);

        // A take, then two aggregates
        let prql: &str = r###"
        from employees
        take 20
        filter country == "USA"
        aggregate [sal = average salary]
        aggregate [sal = average sal]
        sort sal
        "###;

        let pipeline = parse_and_resolve(prql)?;
        let queries = atomic_pipelines_of_pipeline(pipeline, &mut context)?;
        assert_eq!(queries.len(), 3);

        // A take, then a select
        let prql: &str = r###"
        from employees
        take 20
        select first_name
        "###;

        let pipeline = parse_and_resolve(prql)?;
        let queries = atomic_pipelines_of_pipeline(pipeline, &mut context)?;
        assert_eq!(queries.len(), 1);
        Ok(())
    }

    #[test]
    fn test_sql_of_ast_1() -> Result<()> {
        let query: Query = parse(
            r###"
        from employees
        filter country == "USA"
        group [title, country] (
            aggregate [average salary]
        )
        sort title
        take 20
        "###,
        )?;

        let sql = resolve_and_translate(query)?;
        assert_display_snapshot!(sql,
            @r###"
        SELECT
          title,
          country,
          AVG(salary)
        FROM
          employees
        WHERE
          country = 'USA'
        GROUP BY
          title,
          country
        ORDER BY
          title
        LIMIT
          20
        "###
        );
        Ok(())
    }

    #[test]
    fn test_sql_of_ast_2() -> Result<()> {
        let query: Query = parse(
            r###"
        from employees
        aggregate sum_salary = s"count({salary})"
        filter sum_salary > 100
        "###,
        )?;
        let sql = resolve_and_translate(query)?;
        assert_snapshot!(sql, @r###"
        SELECT
          count(salary) AS sum_salary
        FROM
          employees
        HAVING
          count(salary) > 100
        "###);
        assert!(sql.to_lowercase().contains(&"having".to_lowercase()));

        Ok(())
    }

    #[test]
    fn test_prql_to_sql_1() -> Result<()> {
        let query = parse(
            r#"
    from employees
    aggregate [
      count non_null:salary,
      sum salary,
    ]
    "#,
        )?;
        let sql = resolve_and_translate(query)?;
        assert_display_snapshot!(sql,
            @r###"
        SELECT
          COUNT(salary),
          SUM(salary)
        FROM
          employees
        "###
        );
        Ok(())
    }

    #[test]
    fn test_prql_to_sql_2() -> Result<()> {
        let query = parse(
            r#"
from employees
filter country == "USA"                           # Each line transforms the previous result.
derive [                                         # This adds columns / variables.
  gross_salary = salary + payroll_tax,
  gross_cost = gross_salary + benefits_cost      # Variables can use other variables.
]
filter gross_cost > 0
group [title, country] (
    aggregate  [                                 # `by` are the columns to group by.
        average salary,                          # These are aggregation calcs run on each group.
        sum     salary,
        average gross_salary,
        sum     gross_salary,
        average gross_cost,
        sum_gross_cost = sum gross_cost,
        ct = count,
    ]
)
sort sum_gross_cost
filter ct > 200
take 20
"#,
        )?;

        let sql = resolve_and_translate(query)?;
        assert_display_snapshot!(sql);
        Ok(())
    }

    #[test]
    fn test_prql_to_sql_table() -> Result<()> {
        // table
        let query = parse(
            r#"
        table newest_employees = (
            from employees
            sort tenure
            take 50
        )
        table average_salaries = (
            from salaries
            group country (
                aggregate [
                    average_country_salary = average salary
                ]
            )
        )
        from newest_employees
        join average_salaries [country]
        select [name, salary, average_country_salary]
        "#,
        )?;
        let sql = resolve_and_translate(query)?;
        assert_display_snapshot!(sql,
            @r###"
        WITH newest_employees AS (
          SELECT
            employees.*
          FROM
            employees
          ORDER BY
            tenure
          LIMIT
            50
        ), average_salaries AS (
          SELECT
            country,
            AVG(salary) AS average_country_salary
          FROM
            salaries
          GROUP BY
            country
        )
        SELECT
          name,
          average_salaries.salary,
          average_salaries.average_country_salary
        FROM
          newest_employees
          JOIN average_salaries USING(country)
        "###
        );

        Ok(())
    }

    #[test]
    fn test_nonatomic() -> Result<()> {
        // A take, then two aggregates
        let query: Query = parse(
            r###"
            from employees
            take 20
            filter country == "USA"
            group [title, country] (
                aggregate [
                    salary = average salary
                ]
            )
            group [title, country] (
                aggregate [
                    sum_gross_cost = average salary
                ]
            )
            sort sum_gross_cost
        "###,
        )?;

        assert_display_snapshot!((resolve_and_translate(query)?), @r###"
        WITH table_0 AS (
          SELECT
            employees.*
          FROM
            employees
          LIMIT
            20
        ), table_1 AS (
          SELECT
            title,
            country,
            AVG(salary) AS salary
          FROM
            table_0
          WHERE
            country = 'USA'
          GROUP BY
            title,
            country
        )
        SELECT
          title,
          country,
          AVG(salary) AS sum_gross_cost
        FROM
          table_1
        GROUP BY
          title,
          country
        ORDER BY
          sum_gross_cost
        "###);

        Ok(())
    }

    #[test]
    /// Confirm a nonatomic table works.
    fn test_nonatomic_table() -> Result<()> {
        // A take, then two aggregates
        let query = parse(
            r###"
        table a = (
            from employees
            take 50
            aggregate [s"count(*)"]
        )
        from a
        join b [country]
        select [name, salary, average_country_salary]
"###,
        )?;

        assert_display_snapshot!((resolve_and_translate(query)?), @r###"
        WITH table_0 AS (
          SELECT
            employees.*
          FROM
            employees
          LIMIT
            50
        ), a AS (
          SELECT
            count(*)
          FROM
            table_0
        )
        SELECT
          name,
          salary,
          average_country_salary
        FROM
          a
          JOIN b USING(country)
        "###);

        Ok(())
    }

    #[test]
    fn test_table_names_between_splits() {
        let prql = r###"
        from employees
        join d=department [dept_no]
        take 10
        join s=salaries [emp_no]
        select [employees.emp_no, d.name, s.salary]
        "###;
        let result = parse(prql).and_then(resolve_and_translate).unwrap();
        assert_display_snapshot!(result, @r###"
        WITH table_0 AS (
          SELECT
            employees.*,
            d.*,
            dept_no
          FROM
            employees
            JOIN department AS d USING(dept_no)
          LIMIT
            10
        )
        SELECT
          table_0.emp_no,
          table_0.name,
          s.salary
        FROM
          table_0
          JOIN salaries AS s USING(emp_no)
        "###);

        let prql = r###"
        from e=employees
        take 10
        join salaries [emp_no]
        select [e.*, salary]
        "###;
        let result = parse(prql).and_then(resolve_and_translate).unwrap();
        assert_display_snapshot!(result, @r###"
        WITH table_0 AS (
          SELECT
            e.*
          FROM
            employees AS e
          LIMIT
            10
        )
        SELECT
          table_0.*,
          salary
        FROM
          table_0
          JOIN salaries USING(emp_no)
        "###);
    }

    #[test]
    fn test_table_alias() -> Result<()> {
        // Alias on from
        let query: Query = parse(
            r###"
            from e = employees
            join salaries side:left [salaries.emp_no == e.emp_no]
            group [e.emp_no] (
                aggregate [
                    emp_salary = average salary
                ]
            )
            select [e.emp_no, emp_salary]
        "###,
        )?;

        assert_display_snapshot!((resolve_and_translate(query)?), @r###"
        SELECT
          e.emp_no,
          AVG(salary) AS emp_salary
        FROM
          employees AS e
          LEFT JOIN salaries ON salaries.emp_no = e.emp_no
        GROUP BY
          e.emp_no
        "###);
        Ok(())
    }

    #[test]
    fn test_dialects() -> Result<()> {
        // Generic
        let query: Query = parse(
            r###"
        prql dialect:generic
        from Employees
        select [FirstName, `last name`]
        take 3
        "###,
        )?;

        assert_display_snapshot!((resolve_and_translate(query)?), @r###"
        SELECT
          "FirstName",
          "`last name`"
        FROM
          "Employees"
        LIMIT
          3
        "###);

        // SQL server
        let query: Query = parse(
            r###"
        prql dialect:mssql
        from Employees
        select [FirstName, `last name`]
        take 3
        "###,
        )?;

        assert_display_snapshot!((resolve_and_translate(query)?), @r###"
        SELECT
          TOP (3) "FirstName",
          "`last name`"
        FROM
          "Employees"
        "###);

        // MySQL
        let query: Query = parse(
            r###"
        prql dialect:mysql
        from Employees
        select [FirstName, `last name`]
        take 3
        "###,
        )?;

        assert_display_snapshot!((resolve_and_translate(query)?), @r###"
        SELECT
          `FirstName`,
          ```last name```
        FROM
          `Employees`
        LIMIT
          3
        "###);

        Ok(())
    }

    #[test]
    fn test_ident_escaping() -> Result<()> {
        // Generic
        let query: Query = parse(
            r###"
        from `anim"ls`
        derive [`čebela` = BeeName, medved = `bear's_name`]
        "###,
        )?;

        assert_display_snapshot!((resolve_and_translate(query)?), @r###"
        SELECT
          "`anim""ls`".*,
          "BeeName" AS "`čebela`",
          "`bear's_name`" AS medved
        FROM
          "`anim""ls`"
        "###);

        // MySQL
        let query: Query = parse(
            r###"
        prql dialect:mysql

        from `anim"ls`
        derive [`čebela` = BeeName, medved = `bear's_name`]
        "###,
        )?;

        assert_display_snapshot!((resolve_and_translate(query)?), @r###"
        SELECT
          ```anim"ls```.*,
          `BeeName` AS ```čebela```,
          ```bear's_name``` AS medved
        FROM
          ```anim"ls```
        "###);

        Ok(())
    }

    #[test]
    fn test_sorts() -> Result<()> {
        let query: Query = parse(
            r###"
        from invoices
        sort [issued_at, -amount, +num_of_articles]
        "###,
        )?;

        assert_display_snapshot!((resolve_and_translate(query)?), @r###"
        SELECT
          invoices.*
        FROM
          invoices
        ORDER BY
          issued_at,
          amount DESC,
          num_of_articles
        "###);

        Ok(())
    }

    #[test]
    fn test_ranges() -> Result<()> {
        let query: Query = parse(
            r###"
        from employees
        filter (age | in 18..40)
        "###,
        )?;

        assert_display_snapshot!((resolve_and_translate(query)?), @r###"
        SELECT
          employees.*
        FROM
          employees
        WHERE
          age BETWEEN 18
          AND 40
        "###);

        let query: Query = parse(
            r###"
        from employees
        filter (age | in ..40)
        "###,
        )?;

        assert!(resolve_and_translate(query).is_err());

        let query: Query = parse(
            r###"
        from events
        filter (date | in @1776-07-04..@1787-09-17)
        "###,
        )?;

        assert_display_snapshot!((resolve_and_translate(query)?), @r###"
        SELECT
          events.*
        FROM
          events
        WHERE
          date BETWEEN DATE '1776-07-04'
          AND DATE '1787-09-17'
        "###);

        Ok(())
    }

    #[test]
    fn test_interval() -> Result<()> {
        let query: Query = parse(
            r###"
        from projects
        derive first_check_in = start + 10days
        "###,
        )?;

        assert_display_snapshot!((resolve_and_translate(query)?), @r###"
        SELECT
          projects.*,
          start + INTERVAL '10' DAY AS first_check_in
        FROM
          projects
        "###);

        Ok(())
    }

    #[test]
    fn test_dates() -> Result<()> {
        let query: Query = parse(
            r###"
        derive [
            date = @2011-02-01,
            timestamp = @2011-02-01T10:00,
            time = @14:00,
            # datetime = @2011-02-01T10:00<datetime>,
        ]

        "###,
        )?;

        assert_display_snapshot!((resolve_and_translate(query)?), @r###"
        SELECT
          DATE '2011-02-01' AS date,
          TIMESTAMP '2011-02-01T10:00' AS timestamp,
          TIME '14:00' AS time
        "###);

        Ok(())
    }

    #[test]
    fn test_window_functions() {
        let query: Query = parse(
            r###"
        from employees
        group last_name (
            derive count
        )
        "###,
        )
        .unwrap();

        assert_display_snapshot!((resolve_and_translate(query).unwrap()), @r###"
        SELECT
          employees.*,
          COUNT(*) OVER (PARTITION BY last_name)
        FROM
          employees
        "###);

        let query: Query = parse(
            r###"
        from co=cust_order
        join ol=order_line [order_id]
        derive [
          order_month = s"TO_CHAR({co.order_date}, '%Y-%m')",
          order_day = s"TO_CHAR({co.order_date}, '%Y-%m-%d')",
        ]
        group [order_month, order_day] (
          aggregate [
            num_orders = s"COUNT(DISTINCT {co.order_id})",
            num_books = count non_null:ol.book_id,
            total_price = sum ol.price,
          ]
        )
        group [order_month] (
          sort order_day
          window expanding:true (
            derive [running_total_num_books = sum num_books]
          )
        )
        sort order_day
        derive [num_books_last_week = lag 7 num_books]
        "###,
        )
        .unwrap();

        assert_display_snapshot!((resolve_and_translate(query).unwrap()), @r###"
        SELECT
          TO_CHAR(co.order_date, '%Y-%m') AS order_month,
          TO_CHAR(co.order_date, '%Y-%m-%d') AS order_day,
          COUNT(DISTINCT co.order_id) AS num_orders,
          COUNT(ol.book_id) AS num_books,
          SUM(ol.price) AS total_price,
          SUM(COUNT(ol.book_id)) OVER (
            PARTITION BY TO_CHAR(co.order_date, '%Y-%m')
            ORDER BY
              TO_CHAR(co.order_date, '%Y-%m-%d') ROWS BETWEEN UNBOUNDED PRECEDING
              AND CURRENT ROW
          ) AS running_total_num_books,
          LAG(COUNT(ol.book_id), 7) OVER (
            ORDER BY
              TO_CHAR(co.order_date, '%Y-%m-%d') ROWS BETWEEN UNBOUNDED PRECEDING
              AND UNBOUNDED FOLLOWING
          ) AS num_books_last_week
        FROM
          cust_order AS co
          JOIN order_line AS ol USING(order_id)
        GROUP BY
          TO_CHAR(co.order_date, '%Y-%m'),
          TO_CHAR(co.order_date, '%Y-%m-%d')
        ORDER BY
          order_day
        "###);

        // lag must be recognized as window function, even outside of group context
        // rank must not have two OVER clauses
        let query: Query = parse(
            r###"
        from daily_orders
        derive [last_week = lag 7 num_orders]
        group month ( derive [total_month = sum num_orders])
        "###,
        )
        .unwrap();

        assert_display_snapshot!((resolve_and_translate(query).unwrap()), @r###"
        SELECT
          daily_orders.*,
          LAG(num_orders, 7) OVER () AS last_week,
          SUM(num_orders) OVER (PARTITION BY month) AS total_month
        FROM
          daily_orders
        "###);

        // sort does not affects into groups, group undoes sorting
        let query: Query = parse(
            r###"
        from daily_orders
        sort day
        group month (derive [total_month = rank])
        derive [last_week = lag 7 num_orders]
        "###,
        )
        .unwrap();
        assert_display_snapshot!((resolve_and_translate(query).unwrap()), @r###"
        SELECT
          daily_orders.*,
          RANK() OVER (PARTITION BY month) AS total_month,
          LAG(num_orders, 7) OVER () AS last_week
        FROM
          daily_orders
        ORDER BY
          day
        "###);

        // sort does not leak out of groups
        let query: Query = parse(
            r###"
        from daily_orders
        sort day
        group month (sort num_orders | window expanding:true (derive rank))
        derive [num_orders_last_week = lag 7 num_orders]
        "###,
        )
        .unwrap();
        assert_display_snapshot!((resolve_and_translate(query).unwrap()), @r###"
        SELECT
          daily_orders.*,
          RANK() OVER (
            PARTITION BY month
            ORDER BY
              num_orders ROWS BETWEEN UNBOUNDED PRECEDING
              AND CURRENT ROW
          ),
          LAG(num_orders, 7) OVER () AS num_orders_last_week
        FROM
          daily_orders
        "###);
    }

    #[test]
    fn test_window_functions_2() {
        // detect sum as a window function, even without group or window
        assert_display_snapshot!((resolve_and_translate(parse(r###"
        from foo
        derive [a = sum b]
        group c (
            derive [d = sum b]
        )
        "###,
        ).unwrap()).unwrap()), @r###"
        SELECT
          foo.*,
          SUM(b) OVER () AS a,
          SUM(b) OVER (PARTITION BY c) AS d
        FROM
          foo
        "###);

        assert_display_snapshot!((resolve_and_translate(parse(r###"
        from foo
        window expanding:true (
            derive [running_total = sum b]
        )
        "###,
        ).unwrap()).unwrap()), @r###"
        SELECT
          foo.*,
          SUM(b) OVER (
            ROWS BETWEEN UNBOUNDED PRECEDING
            AND CURRENT ROW
          ) AS running_total
        FROM
          foo
        "###);

        assert_display_snapshot!((resolve_and_translate(parse(r###"
        from foo
        window rolling:3 (
            derive [last_three = sum b]
        )
        "###,
        ).unwrap()).unwrap()), @r###"
        SELECT
          foo.*,
          SUM(b) OVER (
            ROWS BETWEEN 2 PRECEDING
            AND CURRENT ROW
          ) AS last_three
        FROM
          foo
        "###);

        assert_display_snapshot!((resolve_and_translate(parse(r###"
        from foo
        window rows:0..4 (
            derive [next_four_rows = sum b]
        )
        "###,
        ).unwrap()).unwrap()), @r###"
        SELECT
          foo.*,
          SUM(b) OVER (
            ROWS BETWEEN CURRENT ROW
            AND 4 FOLLOWING
          ) AS next_four_rows
        FROM
          foo
        "###);

        assert_display_snapshot!((resolve_and_translate(parse(r###"
        from foo
        sort day
        window range:-4..4 (
            derive [next_four_days = sum b]
        )
        "###,
        ).unwrap()).unwrap()), @r###"
        SELECT
          foo.*,
          SUM(b) OVER (
            ORDER BY
              day RANGE BETWEEN 4 PRECEDING
              AND 4 FOLLOWING
          ) AS next_four_days
        FROM
          foo
        "###);

        // TODO: add test for preceding
    }

    #[test]
    fn test_strings() -> Result<()> {
        let query: Query = parse(
            r###"
        derive [
            x = "two households'",
            y = 'two households"',
            z = f"a {x} b' {y} c",
            v = f'a {x} b" {y} c',
        ]
        "###,
        )?;

        assert_display_snapshot!((resolve_and_translate(query)?), @r###"
        SELECT
          'two households''' AS x,
          'two households"' AS y,
          CONCAT(
            'a ',
            'two households''',
            ' b'' ',
            'two households"',
            ' c'
          ) AS z,
          CONCAT(
            'a ',
            'two households''',
            ' b" ',
            'two households"',
            ' c'
          ) AS v
        "###);

        Ok(())
    }

    #[test]
    fn test_filter() {
        // https://github.com/prql/prql/issues/469
        let query: Query = parse(
            r###"
        from employees
        filter [age > 25, age < 40]
        "###,
        )
        .unwrap();

        assert!(resolve_and_translate(query).is_err());

        assert_display_snapshot!((resolve_and_translate(parse(r###"
        from employees
        filter age > 25 and age < 40
        "###,
        ).unwrap()).unwrap()), @r###"
        SELECT
          employees.*
        FROM
          employees
        WHERE
          age > 25
          AND age < 40
        "###);

        assert_display_snapshot!((resolve_and_translate(parse(r###"
        from employees
        filter age > 25
        filter age < 40
        "###,
        ).unwrap()).unwrap()), @r###"
        SELECT
          employees.*
        FROM
          employees
        WHERE
          age > 25
          AND age < 40
        "###);
    }

    #[test]
    fn test_nulls() -> Result<()> {
        assert_display_snapshot!((resolve_and_translate(parse(r###"
        from employees
        select amount = null
        "###,
        )?)?), @r###"
        SELECT
          NULL AS amount
        FROM
          employees
        "###);

        // coalesce
        assert_display_snapshot!((resolve_and_translate(parse(r###"
        from employees
        derive amount = amount + 2 ?? 3 * 5
        "###,
        )?)?), @r###"
        SELECT
          employees.*,
          COALESCE(amount + 2, 3 * 5) AS amount
        FROM
          employees
        "###);

        // IS NULL
        assert_display_snapshot!((resolve_and_translate(parse(r###"
        from employees
        filter first_name == null and null == last_name
        "###,
        )?)?), @r###"
        SELECT
          employees.*
        FROM
          employees
        WHERE
          first_name IS NULL
          AND last_name IS NULL
        "###);

        // IS NOT NULL
        assert_display_snapshot!((resolve_and_translate(parse(r###"
        from employees
        filter first_name != null and null != last_name
        "###,
        )?)?), @r###"
        SELECT
          employees.*
        FROM
          employees
        WHERE
          first_name IS NOT NULL
          AND last_name IS NOT NULL
        "###);

        Ok(())
    }

    #[test]
    fn test_range() -> Result<()> {
        assert_display_snapshot!((resolve_and_translate(parse(r###"
        from employees
        take ..10
        "###,
        )?)?), @r###"
        SELECT
          employees.*
        FROM
          employees
        LIMIT
          10
        "###);

        assert_display_snapshot!((resolve_and_translate(parse(r###"
        from employees
        take 5..10
        "###,
        )?)?), @r###"
        SELECT
          employees.*
        FROM
          employees
        LIMIT
          6 OFFSET 4
        "###);

        assert_display_snapshot!((resolve_and_translate(parse(r###"
        from employees
        take 5..
        "###,
        )?)?), @r###"
        SELECT
          employees.*
        FROM
          employees OFFSET 4
        "###);

        // should be one SELECT
        assert_display_snapshot!((resolve_and_translate(parse(r###"
        from employees
        take 11..20
        take 1..5
        "###,
        )?)?), @r###"
        SELECT
          employees.*
        FROM
          employees
        LIMIT
          5 OFFSET 10
        "###);

        // should be two SELECTs
        assert_display_snapshot!((resolve_and_translate(parse(r###"
        from employees
        take 11..20
        sort name
        take 1..5
        "###,
        )?)?), @r###"
        WITH table_0 AS (
          SELECT
            employees.*
          FROM
            employees
          LIMIT
            10 OFFSET 10
        )
        SELECT
          table_0.*
        FROM
          table_0
        ORDER BY
          name
        LIMIT
          5
        "###);

        Ok(())
    }

    #[test]
    fn test_distinct() {
        // window functions cannot materialize into where statement: CTE is needed
        assert_display_snapshot!((resolve_and_translate(parse(r###"
        from employees
        derive rn = row_number
        filter rn > 2
        "###,
        ).unwrap()).unwrap()), @r###"
        WITH table_0 AS (
          SELECT
            employees.*,
            ROW_NUMBER() OVER () AS rn
          FROM
            employees
        )
        SELECT
          table_0.*
        FROM
          table_0
        WHERE
          rn > 2
        "###);

        // basic distinct
        assert_display_snapshot!((resolve_and_translate(parse(r###"
        from employees
        select first_name
        group first_name (take 1)
        "###,
        ).unwrap()).unwrap()), @r###"
        SELECT
          DISTINCT first_name
        FROM
          employees
        "###);

        // distinct on two columns
        assert_display_snapshot!((resolve_and_translate(parse(r###"
        from employees
        select [first_name, last_name]
        group [first_name, last_name] (take 1)
        "###,
        ).unwrap()).unwrap()), @r###"
        SELECT
          DISTINCT first_name,
          last_name
        FROM
          employees
        "###);

        // TODO: this should not use DISTINCT but ROW_NUMBER and WHERE, because we want
        // row  distinct only over first_name and last_name.
        assert_display_snapshot!((resolve_and_translate(parse(r###"
        from employees
        group [first_name, last_name] (take 1)
        "###,
        ).unwrap()).unwrap()), @r###"
        SELECT
          DISTINCT employees.*
        FROM
          employees
        "###);

        // head
        assert_display_snapshot!((resolve_and_translate(parse(r###"
        from employees
        group department (take 3)
        "###,
        ).unwrap()).unwrap()), @r###"
        WITH table_0 AS (
          SELECT
            employees.*,
            ROW_NUMBER() OVER (PARTITION BY department) AS _rn
          FROM
            employees
        )
        SELECT
          table_0.*
        FROM
          table_0
        WHERE
          _rn <= 3
        "###);

        assert_display_snapshot!((resolve_and_translate(parse(r###"
        from employees
        group department (sort salary | take 2..3)
        "###,
        ).unwrap()).unwrap()), @r###"
        WITH table_0 AS (
          SELECT
            employees.*,
            ROW_NUMBER() OVER (
              PARTITION BY department
              ORDER BY
                salary
            ) AS _rn
          FROM
            employees
        )
        SELECT
          table_0.*
        FROM
          table_0
        WHERE
          _rn BETWEEN 2
          AND 3
        "###);
    }

    #[test]
    fn test_dbt_query() {
        assert_display_snapshot!((resolve_and_translate(parse(r###"
        from {{ ref('stg_orders') }}
        aggregate (min order_id)
        "###,
        ).unwrap()).unwrap()), @r###"
        SELECT
          MIN(order_id)
        FROM
          {{ ref('stg_orders') }}
        "###);
    }

    #[test]
    fn test_pipelines() {
        assert_display_snapshot!((resolve_and_translate(parse(r###"
        from employees
        group dept (take 1)
        "###,
        ).unwrap()).unwrap()), @r###"
        SELECT
          DISTINCT employees.*
        FROM
          employees
        "###);
    }
}
