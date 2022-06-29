use ariadne::{Config, Label, Report, ReportKind, Source};
use serde::{Deserialize, Serialize};
use std::error::Error as StdError;
use std::fmt::{self, Debug, Display, Formatter, Write};
use std::ops::{Add, Range};

use crate::parser::PestError;
#[derive(Debug, Clone, PartialEq, Copy, Serialize, Deserialize)]
pub struct Span {
    pub start: usize,
    pub end: usize,
}

#[derive(Debug, Clone)]
pub struct Error {
    pub span: Option<Span>,
    pub reason: Reason,
    pub help: Option<String>,
}

#[derive(Debug)]
pub struct SourceLocation {
    /// Line and column
    pub start: (usize, usize),

    /// Line and column
    pub end: (usize, usize),
}

#[derive(Debug, Clone)]
pub enum Reason {
    Simple(String),
    Expected {
        who: Option<String>,
        expected: String,
        found: String,
    },
    Unexpected {
        found: String,
    },
    NotFound {
        name: String,
        namespace: String,
    },
}

impl Error {
    pub fn new(reason: Reason) -> Self {
        Error {
            span: None,
            reason,
            help: None,
        }
    }

    pub fn with_help<S: Into<String>>(mut self, help: S) -> Self {
        self.help = Some(help.into());
        self
    }

    pub fn with_span(mut self, span: Option<Span>) -> Self {
        self.span = span;
        self
    }
}

// Needed for anyhow
impl StdError for Error {}

// Needed for StdError
impl Display for Error {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        Debug::fmt(&self, f)
    }
}

pub fn format_error(
    error: anyhow::Error,
    source_id: &str,
    source: &str,
    color: bool,
) -> (String, Option<SourceLocation>) {
    let source = Source::from(source);
    let location = location(&error, &source);

    (error_message(error, source_id, source, color), location)
}

fn location(error: &anyhow::Error, source: &Source) -> Option<SourceLocation> {
    let span = if let Some(error) = error.downcast_ref::<Error>() {
        if let Some(span) = error.span {
            Range::from(span)
        } else {
            return None;
        }
    } else if let Some(error) = error.downcast_ref::<PestError>() {
        pest::as_range(error)
    } else {
        return None;
    };

    let start = source.get_offset_line(span.start)?;
    let end = source.get_offset_line(span.end)?;

    Some(SourceLocation {
        start: (start.1, start.2),
        end: (end.1, end.2),
    })
}

fn error_message(error: anyhow::Error, source_id: &str, source: Source, color: bool) -> String {
    let config = Config::default().with_color(color);

    if let Some(error) = error.downcast_ref::<Error>() {
        let message = error.reason.message();

        if let Some(span) = error.span {
            let span = Range::from(span);

            let mut report = Report::build(ReportKind::Error, source_id, span.start)
                .with_config(config)
                .with_message("")
                .with_label(Label::new((source_id, span)).with_message(&message));

            if let Some(help) = &error.help {
                report.set_help(help);
            }

            let mut out = Vec::new();
            report
                .finish()
                .write((source_id, source), &mut out)
                .unwrap();

            return String::from_utf8(out).unwrap();
        } else {
            let mut out = format!("Error: {message}");

            if let Some(help) = &error.help {
                out = format!("{out}\n  help: {help}");
            }

            return out;
        }
    }

    if let Some(error) = error.downcast_ref::<PestError>() {
        let span = pest::as_range(error);
        let mut out = Vec::new();

        Report::build(ReportKind::Error, source_id, span.start)
            .with_config(config)
            .with_message("during parsing")
            .with_label(Label::new((source_id, span)).with_message(pest::as_message(error)))
            .finish()
            .write((source_id, source), &mut out)
            .unwrap();

        return String::from_utf8(out).unwrap();
    }

    // default to basic Display
    let mut out = String::new();
    write!(&mut out, "{:#?}", error).unwrap();
    out
}

impl Reason {
    fn message(&self) -> String {
        match self {
            Reason::Simple(text) => text.clone(),
            Reason::Expected {
                who,
                expected,
                found,
            } => {
                let who = who.clone().map(|x| format!("{x} ")).unwrap_or_default();
                format!("{who}expected {expected}, but found {found}")
            }
            Reason::Unexpected { found } => format!("unexpected {found}"),
            Reason::NotFound { name, namespace } => format!("{namespace} `{name}` not found"),
        }
    }
}

mod pest {
    use pest::error::{ErrorVariant, InputLocation};
    use std::ops::Range;

    use crate::parser::{PestError, PestRule};

    pub fn as_range(error: &PestError) -> Range<usize> {
        match error.location {
            InputLocation::Pos(r) => r..r + 1,
            InputLocation::Span(r) => r.0..r.1,
        }
    }

    pub fn as_message(error: &PestError) -> String {
        match error.variant {
            ErrorVariant::ParsingError {
                ref positives,
                ref negatives,
            } => parsing_error_message(positives, negatives),
            ErrorVariant::CustomError { ref message } => message.clone(),
        }
    }

    fn parsing_error_message(positives: &[PestRule], negatives: &[PestRule]) -> String {
        match (negatives.is_empty(), positives.is_empty()) {
            (false, false) => format!(
                "unexpected {}; expected {}",
                enumerate(negatives),
                enumerate(positives)
            ),
            (false, true) => format!("unexpected {}", enumerate(negatives)),
            (true, false) => format!("expected {}", enumerate(positives)),
            (true, true) => "unknown parsing error".to_owned(),
        }
    }

    fn enumerate(rules: &[PestRule]) -> String {
        match rules.len() {
            1 => format!("{:?}", rules[0]),
            2 => format!("{:?} or {:?}", rules[0], rules[1]),
            l => {
                let separated = rules
                    .iter()
                    .take(l - 1)
                    .map(|x| format!("{:?}", x))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("{}, or {:?}", separated, rules[l - 1])
            }
        }
    }
}

impl From<Span> for Range<usize> {
    fn from(a: Span) -> Self {
        a.start..a.end
    }
}

impl Add<Span> for Span {
    type Output = Span;

    fn add(self, rhs: Span) -> Span {
        Span {
            start: self.start.min(rhs.start),
            end: self.end.max(rhs.end),
        }
    }
}

pub trait WithErrorInfo {
    fn with_help<S: Into<String>>(self, help: S) -> Self;

    fn with_span(self, span: Option<Span>) -> Self;
}

impl<T> WithErrorInfo for Result<T, Error> {
    fn with_help<S: Into<String>>(self, help: S) -> Self {
        self.map_err(|e| e.with_help(help))
    }

    fn with_span(self, span: Option<Span>) -> Self {
        self.map_err(|e| e.with_span(span))
    }
}
