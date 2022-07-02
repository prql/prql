use std::cmp::Ordering;
use std::collections::HashMap;

use anyhow::{bail, Result};
use itertools::Itertools;

use crate::ast::ast_fold::*;
use crate::error::{Error, Reason};
use crate::{ast::*, Context, Declaration};

pub fn resolve_type(node: Node) -> Result<Node> {
    let mut resolver = TypeResolver {};

    resolver.fold_node(node)
}

pub struct TypeResolver {}

impl TypeResolver {
    // fn validate_function_defs(&mut self) -> Result<()> {
    //     let function_defs: Vec<_> = (self.context.declarations.0.iter())
    //         .enumerate()
    //         .filter(|(_, (decl, _))| matches!(decl, Declaration::Function(_)))
    //         .map(|(id, _)| id)
    //         .collect();

    //     for id in function_defs {
    //         let mut func_def = self.context.declarations.take(id).into_function().unwrap();

    //         func_def.body = Box::new(self.fold_node(*func_def.body)?);

    //         let expected = func_def.return_ty.unwrap_or(Ty::Infer);

    //         let assumed = validate_type(&func_def.body, &expected, || Some(func_def.name.clone()))?;

    //         func_def.return_ty = Some(assumed);

    //         let decl = Declaration::Function(func_def);
    //         self.context.declarations.replace(id, decl);
    //     }

    //     Ok(())
    // }
}

impl AstFold for TypeResolver {
    fn fold_node(&mut self, mut node: Node) -> Result<Node> {
        if node.ty.is_some() {
            return Ok(node);
        }

        let ty = match node.item {
            Item::Literal(ref literal) => match literal {
                Literal::Null => Ty::Infer,
                Literal::Integer(_) => TyLit::Integer.into(),
                Literal::Float(_) => TyLit::Float.into(),
                Literal::Boolean(_) => TyLit::Bool.into(),
                Literal::String(_) => TyLit::String.into(),
                Literal::Date(_) => TyLit::Date.into(),
                Literal::Time(_) => TyLit::Time.into(),
                Literal::Timestamp(_) => TyLit::Timestamp.into(),
            },

            Item::Assign(_) => Ty::Assigns,

            Item::NamedArg(_) | Item::Windowed(_) => {
                // assume type of inner expr
                node.item = self.fold_item(node.item)?;

                match &node.item {
                    Item::NamedArg(ne) => ne.expr.ty.clone().unwrap(),
                    Item::Windowed(w) => w.expr.ty.clone().unwrap(),
                    _ => unreachable!(),
                }
            }

            Item::Ident(_) | Item::Pipeline(_) | Item::FuncCall(_) => Ty::Unresolved,

            Item::SString(_) => Ty::Infer, // TODO
            Item::FString(_) => TyLit::String.into(),
            Item::Interval(_) => Ty::Infer, // TODO
            Item::Range(_) => Ty::Infer,

            _ => {
                // pass trough
                node.item = self.fold_item(node.item)?;
                Ty::Infer
            }
        };

        node.ty = Some(ty);
        Ok(node)
    }
}

fn too_many_arguments(call: &FuncCall, expected_len: usize, passed_len: usize) -> Error {
    let err = Error::new(Reason::Expected {
        who: Some(format!("{}", call.name.item)),
        expected: format!("{} arguments", expected_len),
        found: format!("{}", passed_len),
    });
    if passed_len >= 2 {
        err.with_help(format!(
            "If you are calling a function, you may want to add parentheses `{} [{:?} {:?}]`",
            call.name.item, call.args[0], call.args[1]
        ))
    } else {
        err
    }
}

/// Validates that found node has expected type. Returns assumed type of the node.
pub fn validate_type<F>(found: &Node, expected: &Ty, who: F) -> Result<Ty, Error>
where
    F: FnOnce() -> Option<String>,
{
    let found_ty = found.ty.clone().unwrap();

    // infer
    if let Ty::Infer = expected {
        return Ok(found_ty);
    }
    if let Ty::Infer = found_ty {
        return Ok(expected.clone());
    }

    let expected_is_above = matches!(
        expected.partial_cmp(&found_ty),
        Some(Ordering::Equal | Ordering::Greater)
    );
    if !expected_is_above {
        return Err(Error::new(Reason::Expected {
            who: who(),
            expected: format!("type `{}`", expected),
            found: format!("type `{}`", found_ty),
        })
        .with_span(found.span));
    }
    Ok(expected.clone())
}

pub fn type_of_func_def(def: &FuncDef) -> TyFunc {
    TyFunc {
        args: def
            .positional_params
            .iter()
            .map(|a| a.ty.clone().unwrap_or(Ty::Infer))
            .collect(),
        named: def
            .named_params
            .iter()
            .map(|a| (a.name.clone(), a.ty.clone().unwrap_or(Ty::Infer)))
            .collect(),
        return_ty: Box::new(def.return_ty.clone().unwrap_or(Ty::Infer)),
    }
}
