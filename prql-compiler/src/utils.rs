use anyhow::{anyhow, Result};
use itertools::{Itertools, Position};

use crate::ast::Node;
use crate::error::{Error, Reason};

// Inspired by version in sqlparser-rs; I'm surprised there isn't a version in
// the stdlib / Itertools.
/// Returns the only element of an Iterator, or an error if it has more than one element.
pub trait IntoOnly
where
    Self: IntoIterator,
{
    fn into_only(self) -> Result<Self::Item>;
}

impl<T, I> IntoOnly for I
where
    I: IntoIterator<Item = T>,
    // See below re using Debug.
    // I: std::fmt::Debug,
    // <I as IntoIterator>::IntoIter: std::fmt::Debug,
{
    fn into_only(self) -> Result<T> {
        match self.into_iter().with_position().next() {
            Some(Position::Only(item)) => Ok(item),
            // Can't get the debug of the iterator because it's already
            // consumed; is there a way around this? I guess we could show
            // the items after the second, which is kinda weird.
            Some(Position::First(_)) => Err(anyhow!("Expected only one element, but found more.",)),
            None => Err(anyhow!("Expected one element, but found none.",)),
            _ => unreachable!(),
        }
    }
}

pub trait IntoOnlyNode {
    fn into_only_node(self, who: &str, occupation: &str) -> Result<Node, Error>;
}

impl IntoOnlyNode for Vec<Node> {
    fn into_only_node(mut self, who: &str, occupation: &str) -> Result<Node, Error> {
        match self.len() {
            1 => Ok(self.remove(0)),
            0 => Err(Error {
                reason: Reason::Expected {
                    who: Some(who.to_string()),
                    expected: format!("only one {occupation}"),
                    found: "none".to_string(),
                },
                span: None,
                help: None,
            }),
            _ => Err(Error {
                reason: Reason::Expected {
                    who: Some(who.to_string()),
                    expected: format!("only one {occupation}"),
                    found: "more".to_string(),
                },
                span: self[1].span,
                help: None,
            }),
        }
    }
}

pub trait Only<T> {
    fn only(&self) -> Result<&T>;
}

impl<T> Only<T> for [T]
where
    T: std::fmt::Debug,
{
    fn only(&self) -> Result<&T> {
        if self.len() == 1 {
            Ok(self.first().unwrap())
        } else {
            Err(anyhow!("Expected 1 item, got {}; {:?}", self.len(), self))
        }
    }
}

#[cfg(test)]
pub fn diff(a: &str, b: &str) -> String {
    use similar::TextDiff;
    TextDiff::from_lines(a, b).unified_diff().to_string()
}

pub trait OrMap<T> {
    /// Merges two options into one using `f`.
    /// If one of the options is None, results defaults to the other one.
    fn or_map<F>(self, b: Self, f: F) -> Self
    where
        F: FnOnce(T, T) -> T;
}

impl<T> OrMap<T> for Option<T> {
    fn or_map<F>(self, b: Self, f: F) -> Self
    where
        F: FnOnce(T, T) -> T,
    {
        match (self, b) {
            (Some(a), Some(b)) => Some(f(a, b)),
            (a, None) => a,
            (None, b) => b,
        }
    }
}
