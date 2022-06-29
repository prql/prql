use anyhow::{Context, Result};
use enum_as_inner::EnumAsInner;
use serde::{Deserialize, Serialize};
use std::fmt::{Debug, Display};

use crate::ast::*;
use crate::error::Span;

#[derive(Debug, EnumAsInner, Clone, Serialize, Deserialize)]
pub enum Declaration {
    Expression(Box<Node>),
    ExternRef {
        /// Table can be None if we are unable to determine from which table this column
        /// is from.
        table: Option<usize>,
        /// Full identifier when table is None, only variable name when table is known.
        variable: String,
    },
    Table(String),
    Function(FuncDef),
}

#[derive(Default, Serialize, Deserialize, Clone)]
pub struct Declarations(pub Vec<(Declaration, Option<Span>)>);

impl Declarations {
    pub fn get(&self, id: usize) -> &Declaration {
        &self.0[id].0
    }

    pub fn get_func(&self, id: Option<usize>) -> Result<&FuncDef> {
        let id = id.context("unresolved function def?")?;
        let (decl, _span) = &self.0[id];
        decl.as_function().context("expected function definition?")
    }

    pub fn push(&mut self, dec: Declaration, span: Option<Span>) -> usize {
        self.0.push((dec, span));
        self.0.len() - 1
    }

    pub(crate) fn replace(&mut self, id: usize, decl: Declaration) {
        let reference = self.0.get_mut(id).unwrap();
        *reference = (decl, None);
    }

    pub(crate) fn replace_expr(&mut self, id: usize, expr: Node) {
        self.replace(id, Declaration::Expression(Box::new(expr)));
    }

    /// Takes a declaration with minimal memory copying. A dummy node is left in place.
    pub(super) fn take(&mut self, id: usize) -> Declaration {
        let (decl, _) = self.0.get_mut(id).unwrap();

        let dummy = Node::from(Item::Literal(Literal::Null));
        let dummy = Declaration::Expression(Box::new(dummy));
        std::mem::replace(decl, dummy)
    }
}

impl From<Declaration> for anyhow::Error {
    fn from(dec: Declaration) -> Self {
        // panic!("Unexpected declaration type: {dec:?}");
        anyhow::anyhow!("Unexpected declaration type: {dec:?}")
    }
}

impl Debug for Declarations {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (i, (d, _)) in self.0.iter().enumerate() {
            match d {
                Declaration::Expression(v) => {
                    writeln!(f, "[{i:3}]: expr  `{}`", v.item)?;
                }
                Declaration::ExternRef { table, variable } => {
                    writeln!(f, "[{i:3}]: col   `{variable}` from table {table:?}")?;
                }
                Declaration::Table(name) => {
                    writeln!(f, "[{i:3}]: table `{name}`")?;
                }
                Declaration::Function(func) => {
                    writeln!(f, "[{i:3}]: func  `{}`", func.name)?;
                }
            }
        }
        Ok(())
    }
}

impl Display for Declaration {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Declaration::Expression(node) => write!(f, "{}", node.item),
            Declaration::ExternRef { table: _, variable } => write!(f, "<extern> {variable}"),
            Declaration::Table(t) => write!(f, "table {t} = ?"),
            Declaration::Function(func) => {
                let str = format!("{}", Item::FuncDef(func.clone()));
                f.write_str(&str[..str.len() - 2])
            }
        }
    }
}
