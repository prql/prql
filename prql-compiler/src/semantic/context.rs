use itertools::Itertools;
use serde::{Deserialize, Serialize};
use std::collections::HashSet;
use std::fmt::Debug;

use super::scope::NS_PARAM;
use super::{Declaration, Declarations, Scope};
use crate::{ast::*, split_var_name};
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

    pub fn lookup_name(&mut self, name: &str, span: Option<Span>) -> Result<usize, String> {
        let (namespace, variable) = split_var_name(name);

        if let Some(decls) = self.scope.variables.get(name) {
            // lookup the inverse index

            match decls.len() {
                0 => unreachable!("inverse index contains empty lists?"),

                // single match, great!
                1 => Ok(decls.iter().next().cloned().unwrap()),

                // ambiguous
                _ => {
                    let decls = decls
                        .iter()
                        .map(|d| self.declarations.get(*d))
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

            if let Some(decls) = self.scope.variables.get(&all) {
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
                        let id = self.declare(decl, span);
                        self.scope.add(name.to_string(), id);

                        Ok(id)
                    }

                    // don't report ambiguous variable, database may be able to resolve them
                    _ => {
                        let decl = Declaration::ExternRef {
                            table: None,
                            variable: name.to_string(),
                        };
                        let id = self.declare(decl, span);

                        Ok(id)
                    }
                }
            } else {
                dbg!(&self);
                Err(format!("Unknown name `{name}`"))
            }
        }
    }

    pub fn lookup_namespaces_of(&mut self, variable: &str) -> HashSet<usize> {
        let mut r = HashSet::new();
        if let Some(ns) = self.scope.variables.get(variable) {
            r.extend(ns.clone());
        }
        if let Some(ns) = self.scope.variables.get("*") {
            r.extend(ns.clone());
        }
        r
    }
}

impl Debug for Context {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "{:?}", self.declarations)?;
        writeln!(f, "{:?}", self.scope)
    }
}
