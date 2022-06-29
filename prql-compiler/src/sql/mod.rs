mod distinct;
mod materializer;
mod translator;
mod un_group;

pub use materializer::{materialize, MaterializedFrame};
pub use translator::translate;

use anyhow::Result;

use crate::ast::{Node, Query};
use crate::semantic;

/// Resolve all variable and function calls using SQL stdlib and then translate AST into SQL.
pub fn resolve_and_translate(mut query: Query) -> Result<String> {
    let std_lib = load_std_lib()?;
    let (_, context) = semantic::analyze(std_lib, None)?;

    let (nodes, context) = semantic::analyze(query.nodes, Some(context))?;

    query.nodes = nodes;
    translate(query, context)
}

pub fn load_std_lib() -> Result<Vec<Node>> {
    use crate::parse;
    let std_lib = include_str!("./stdlib.prql");
    Ok(parse(std_lib)?.nodes)
}
