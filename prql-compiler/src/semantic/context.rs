use serde::{Deserialize, Serialize};
use std::fmt::Debug;

use super::scope::NS_PARAM;
use super::{Declaration, Declarations, Scope};
use crate::ast::*;
use crate::error::Span;

/// Context of the pipeline.
#[derive(Default, Serialize, Deserialize, Clone)]
pub struct Context {
    /// Map of all accessible names (for each namespace)
    pub(crate) scope: Scope,

    /// All declarations, even those out of scope
    pub(crate) declarations: Declarations,
}

impl Context {
    pub fn declare(&mut self, dec: Declaration, span: Option<Span>) -> usize {
        self.declarations.push(dec, span)
    }

    pub fn declare_func(&mut self, func_def: FuncDef) -> usize {
        let name = func_def.name.clone();

        let span = func_def.body.span;
        let id = self.declare(Declaration::Function(func_def), span);

        self.scope.add_function(name, id);

        id
    }

    pub fn declare_table(&mut self, name: Ident, alias: Option<String>) -> usize {
        let alias = alias.unwrap_or_else(|| name.clone());

        let table_id = self.declare(Declaration::Table(alias.clone()), None);

        let var_name = format!("{alias}.*");
        self.scope.add(var_name, table_id);
        table_id
    }

    pub fn declare_func_param(&mut self, param: &FuncParam) -> usize {
        let name = param.name.clone();

        // value doesn't matter, it will get overridden anyway
        let mut decl: Node = Item::Literal(Literal::Null).into();
        decl.ty = param.ty.clone();

        let id = self.declare(Declaration::Expression(Box::new(decl)), None);

        self.scope.add(format!("{NS_PARAM}.{name}"), id);

        id
    }
}

impl Debug for Context {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "{:?}", self.declarations)?;
        writeln!(f, "{:?}", self.scope)
    }
}
