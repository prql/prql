//! Transform the parsed AST into a "materialized" AST, by executing functions and
//! replacing variables. The materialized AST is "flat", in the sense that it
//! contains no query-specific logic.
use std::collections::HashMap;
use std::iter::zip;

use crate::ast::ast_fold::*;
use crate::ast::*;

use anyhow::Result;

pub fn materialize(func_def: FuncDef, func_curry: FuncCurry) -> Result<Node> {
    let mut m = Materializer { mapping: HashMap::new() };

    // for each of the params, replace its declared value
    for (param, arg) in zip(func_def.named_params, func_curry.named_args) {
        let id = param.declared_at.unwrap();

        let value = arg.unwrap_or_else(|| param.default_value.unwrap());
        m.mapping.insert(id, value);
    }
    for (param, arg) in zip(func_def.positional_params, func_curry.args) {
        let id = param.declared_at.unwrap();
        let value = arg.item.clone().into();
        m.mapping.insert(id, value);
    }

    m.fold_node(*func_def.body)
}

struct Materializer {
    mapping: HashMap<usize, Node>,
}

impl AstFold for Materializer {
    fn fold_node(&mut self, mut node: Node) -> Result<Node> {
        if let Some(declared_at) = node.declared_at {
            if let Some(with) = self.mapping.get(&declared_at) {
                return Ok(with.clone());
            }
        }
        node.item = self.fold_item(node.item)?;
        Ok(node)
    }
}
