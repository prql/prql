mod complexity;
mod context;
mod declarations;
mod frame;
mod name_resolver;
mod reporting;
mod scope;
mod transforms;
mod type_resolver;

use crate::ast::Node;

pub use self::context::Context;
pub use self::declarations::{Declaration, Declarations};
pub use self::frame::{Frame, FrameColumn};
pub use self::scope::{split_var_name, Scope};
pub use reporting::{collect_frames, label_references};

/// Runs semantic analysis on the query, using current state.
///
/// Note that this removes function declarations from AST and saves them as current context.
pub fn analyze(nodes: Vec<Node>, context: Option<Context>) -> anyhow::Result<(Vec<Node>, Context)> {
    let (nodes, context) = name_resolver::resolve_names(nodes, context)?;
    let (nodes, context) = type_resolver::resolve_types(nodes, context)?;
    let (nodes, context) = transforms::construct_transforms(nodes, context)?;
    let nodes = complexity::determine_complexity(nodes, &context);
    Ok((nodes, context))
}
