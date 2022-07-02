use std::collections::{HashMap, HashSet};

use anyhow::{bail, Result};
use itertools::Itertools;

use crate::ast::ast_fold::*;
use crate::error::{Error, Reason, Span, WithErrorInfo};
use crate::{ast::*, split_var_name, Declaration};

use super::type_resolver::{resolve_type, type_of_func_def, validate_type};
use super::Context;

/// Runs semantic analysis on the query, using current state.
///
/// Note that this removes function declarations from AST and saves them as current context.
pub fn resolve(nodes: Vec<Node>, context: Context) -> Result<(Vec<Node>, Context)> {
    let mut resolver = Resolver { context };

    let nodes = resolver.fold_nodes(nodes)?;

    Ok((nodes, resolver.context))
}

/// Can fold (walk) over AST and for each function call or variable find what they are referencing.
pub struct Resolver {
    pub context: Context,
}

impl AstFold for Resolver {
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
            Item::FuncCall(FuncCall {
                name,
                args,
                named_args,
            }) => {
                // find function
                let curry = match name.item {
                    Item::Ident(name) => {
                        // by function name
                        let id = match self.context.lookup_name(&name, node.span) {
                            Ok(id) => id,
                            Err(e) => bail!(Error::new(Reason::Simple(e)).with_span(node.span)),
                        };

                        // construct an empty curry (this is a "fresh" call)
                        FuncCurry {
                            def_id: id,
                            args: vec![],
                            named_args: vec![],
                        }
                    }

                    Item::FuncCurry(curry) => curry,

                    _ => todo!("throw an error"),
                };

                self.fold_function(curry, args, named_args)?
            }

            Item::Ident(ref ident) => {
                node.declared_at = match self.context.lookup_name(ident, node.span) {
                    Ok(r) => Some(r),
                    Err(e) => bail!(e),
                };

                // convert ident to function without args
                let func_decl = self.context.declarations.get_func(node.declared_at);
                if func_decl.is_ok() {
                    let curry = FuncCurry {
                        def_id: node.declared_at.unwrap(),
                        args: vec![],
                        named_args: vec![],
                    };
                    self.fold_function(curry, vec![], HashMap::new())?
                } else {
                    node
                }
            }

            item => {
                node.item = fold_item(self, item)?;
                node
            }
        };

        if r.ty.is_some() {
            Ok(r)
        } else {
            resolve_type(r)
        }
    }
}

impl Resolver {
    fn fold_function(
        &mut self,
        curry: FuncCurry,
        args: Vec<Node>,
        named_args: HashMap<String, Box<Node>>,
    ) -> Result<Node, anyhow::Error> {
        let id = Some(curry.def_id);
        let func_def = self.context.declarations.get_func(id)?.clone();

        let curry = self.apply_args_to_curry(curry, args, named_args, &func_def)?;
        let args_len = curry.args.len();

        let enough_args = args_len >= func_def.positional_params.len();
        Ok(if enough_args {
            super::materializer::materialize(func_def, curry)?
        } else {
            let mut node = Node::from(Item::FuncCurry(curry));

            let mut ty = type_of_func_def(&func_def);
            ty.args = ty.args[args_len..].to_vec();
            ty.named.clear();
            node.ty = Some(Ty::Function(ty));

            node
        })
    }

    fn apply_args_to_curry(
        &mut self,
        mut curry: FuncCurry,
        args: Vec<Node>,
        named_args: HashMap<Ident, Box<Node>>,
        func_def: &FuncDef,
    ) -> Result<FuncCurry> {
        for arg in args {
            let index = curry.args.len();
            let param = (func_def.positional_params.get(index))
                .ok_or_else(|| anyhow::anyhow!("to much arguments"))?;

            // fold
            let arg = self.fold_node(arg)?;

            // validate type
            if let Some(param_ty) = &param.ty {
                validate_type(&arg, param_ty, || Some(func_def.name.to_string()))?;
            }

            curry.args.push(arg);
        }

        // named arguments are consumed only by the first function (non-curry)
        if !curry.named_args.is_empty() {
            if !named_args.is_empty() {
                bail!("function curry cannot accept named arguments");
            }
        } else {
            curry.named_args = func_def.named_params.iter().map(|_| None).collect();
            for (name, arg) in named_args {
                let (index, param) = func_def
                    .named_params
                    .iter()
                    .find_position(|p| p.name == name)
                    .ok_or_else(|| anyhow::anyhow!("unknown named argument"))?;

                // fold
                let arg = self.fold_node(*arg)?;

                // validate type
                if let Some(param_ty) = &param.ty {
                    validate_type(&arg, param_ty, || Some(func_def.name.to_string()))?;
                }

                curry.named_args[index] = Some(arg);
            }
        }

        Ok(curry)
    }
}
