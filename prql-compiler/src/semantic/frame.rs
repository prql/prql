use std::fmt::{Debug, Formatter};

use anyhow::{anyhow, Result};
use itertools::Itertools;
use serde::{Deserialize, Serialize};

use super::Context;
use crate::ast::{ColumnSort, Item, Node, Transform};

/// Represents the object that is manipulated by the pipeline transforms.
/// Similar to a view in a database or a data frame.
#[derive(Clone, Default, PartialEq, Serialize, Deserialize)]
pub struct Frame {
    pub columns: Vec<FrameColumn>,
    pub sort: Vec<ColumnSort<usize>>,

    pub tables: Vec<usize>,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum FrameColumn {
    All(usize),
    Unnamed(usize),
    Named(String, usize),
}

impl Frame {
    fn push_column(&mut self, name: Option<String>, id: usize) {
        // remove columns with the same name
        if let Some(name) = &name {
            self.columns.retain(|c| match c {
                FrameColumn::Named(n, _) => n != name,
                _ => true,
            })
        }

        let column = if let Some(name) = name {
            FrameColumn::Named(name, id)
        } else {
            FrameColumn::Unnamed(id)
        };
        self.columns.push(column);
    }

    pub fn apply_transform(&mut self, transform: &Transform) -> Result<()> {
        match transform {
            Transform::From(t) => {
                *self = Frame::default();

                let table_id = t
                    .declared_at
                    .ok_or_else(|| anyhow!("unresolved table {t:?}"))?;
                self.tables.push(table_id);
                self.columns.push(FrameColumn::All(table_id));
            }

            Transform::Select(assigns) => {
                self.columns.clear();

                self.apply_assigns(assigns);
            }
            Transform::Derive(assigns) => {
                self.apply_assigns(assigns);
            }
            Transform::Group { pipeline, .. } => {
                self.sort.clear();

                let pipeline = pipeline.item.as_pipeline().unwrap();
                for transform in pipeline.as_transforms().unwrap() {
                    self.apply_transform(transform)?;
                }
            }
            Transform::Window { pipeline, .. } => {
                self.sort.clear();

                let pipeline = pipeline.item.as_pipeline().unwrap();
                for transform in pipeline.as_transforms().unwrap() {
                    self.apply_transform(transform)?;
                }
            }
            Transform::Aggregate { assigns, by } => {
                let old_columns = self.columns.clone();

                self.columns.clear();

                for b in by {
                    let id = b.declared_at.unwrap();
                    let col = old_columns.iter().find(|c| c == &&id);
                    let name = col.and_then(|c| match c {
                        FrameColumn::Named(n, _) => Some(n.clone()),
                        _ => None,
                    });

                    self.push_column(name, id);
                }

                self.apply_assigns(assigns);
            }
            Transform::Join { with, filter, .. } => {
                let table_id = with
                    .declared_at
                    .ok_or_else(|| anyhow!("unresolved table {with:?}"))?;
                self.tables.push(table_id);
                self.columns.push(FrameColumn::All(table_id));

                match filter {
                    crate::ast::JoinFilter::On(_) => {}
                    crate::ast::JoinFilter::Using(nodes) => {
                        for node in nodes {
                            let name = node.item.as_ident().unwrap().clone();
                            let id = node.declared_at.unwrap();
                            self.push_column(Some(name), id);
                        }
                    }
                }
            }
            Transform::Sort(sort) => {
                self.sort = extract_sorts(sort)?;
            }
            Transform::Filter(_) | Transform::Take { .. } | Transform::Unique => {}
        }
        Ok(())
    }

    fn apply_assigns(&mut self, assigns: &[Node]) {
        for node in assigns {
            match &node.item {
                Item::Ident(name) => {
                    let id = node.declared_at.unwrap();

                    if name == "<unnamed>" {
                        self.push_column(None, id);
                    } else {
                        self.push_column(Some(name.clone()), id);
                    }
                }
                item => unreachable!(
                    "assign must contain only idents after being resolved, but got `{item}`",
                ),
            }
        }
    }

    pub fn get_column_names(&self, context: &Context) -> Vec<Option<String>> {
        self.columns
            .iter()
            .map(|col| match col {
                FrameColumn::All(namespace) => {
                    let (table, _) = &context.declarations.0[*namespace];
                    let table = table.as_table().map(|x| x.as_str()).unwrap_or("");
                    Some(format!("{table}.*"))
                }
                FrameColumn::Unnamed(_) => None,
                FrameColumn::Named(name, _) => Some(name.clone()),
            })
            .collect()
    }
}

pub(super) fn extract_sorts(sort: &[ColumnSort]) -> Result<Vec<ColumnSort<usize>>> {
    sort.iter()
        .map(|s| {
            Ok(ColumnSort {
                column: (s.column.declared_at)
                    .ok_or_else(|| anyhow!("Unresolved ident in sort?"))?,
                direction: s.direction.clone(),
            })
        })
        .try_collect()
}

impl Debug for Frame {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "[")?;
        for t_col in &self.columns {
            match t_col {
                FrameColumn::All(ns) => write!(f, " {ns}.* ")?,
                FrameColumn::Named(name, id) => write!(f, " {name}:{id} ")?,
                FrameColumn::Unnamed(id) => write!(f, " {id} ")?,
            }
        }
        writeln!(f, "]")
    }
}

impl PartialEq<usize> for FrameColumn {
    fn eq(&self, other: &usize) -> bool {
        match self {
            FrameColumn::All(_) => false,
            FrameColumn::Unnamed(id) | FrameColumn::Named(_, id) => id == other,
        }
    }
}
