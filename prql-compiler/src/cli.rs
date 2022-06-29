use anyhow::{Error, Result};
use ariadne::Source;
use clap::{ArgEnum, Args, Parser};
use clio::{Input, Output};
use itertools::Itertools;
use std::{
    io::{Read, Write},
    ops::Range,
};

use crate::sql::load_std_lib;
use crate::{ast::Item, parse};
use crate::{
    error::{self, Span},
    semantic::{Context, Frame},
};
use crate::{semantic, sql::resolve_and_translate};

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, ArgEnum)]
enum Format {
    /// Abstract syntax tree (parse)
    Ast,

    /// Formatted PRQL
    Fmt,

    /// PRQL with annotated references to variables and functions
    #[clap(name = "prql-refs")]
    PrqlReferences,

    /// PRQL with current table layout
    PrqlFrames,

    Sql,
}

#[derive(Parser)]
#[clap(name = env!("CARGO_PKG_NAME"), about, version)]
pub enum Cli {
    Compile(CompileCommand),
}

#[derive(Args)]
/// Compile a PRQL string into a SQL string.
///
/// See https://github.com/prql/prql for more information.
pub struct CompileCommand {
    #[clap(default_value="-", parse(try_from_os_str = Input::try_from))]
    input: Input,

    #[clap(short, long, default_value = "-", parse(try_from_os_str = Output::try_from))]
    output: Output,

    #[clap(short, long, arg_enum, default_value = "sql")]
    format: Format,
}

fn is_stdin(input: &Input) -> bool {
    input.path() == "-"
}

impl Cli {
    pub fn execute(&mut self) -> Result<(), Error> {
        match self {
            Cli::Compile(command) => {
                // Don't wait without a prompt when running `prql-compiler compile` —
                // it's confusing whether it's waiting for input or not. This
                // offers the prompt.
                if is_stdin(&command.input) && atty::is(atty::Stream::Stdin) {
                    println!("Enter PRQL, then ctrl-d:");
                    println!();
                }

                let mut source = String::new();
                command.input.read_to_string(&mut source)?;
                let source_id = (*command.input.path()).to_str().unwrap();

                let res = compile_to(command.format, &source);

                match res {
                    Ok(buf) => {
                        command.output.write_all(&buf)?;
                    }
                    Err(e) => {
                        print!("{:}", error::format_error(e, source_id, &source, true).0);
                        std::process::exit(1)
                    }
                };
            }
        }

        Ok(())
    }
}

fn compile_to(format: Format, source: &str) -> Result<Vec<u8>, Error> {
    Ok(match format {
        Format::Ast => {
            let ast = parse(source)?;

            serde_yaml::to_vec(&ast)?
        }
        Format::Fmt => {
            let query = parse(source)?;
            let query = Item::Query(query);

            format!("{query}").as_bytes().to_vec()
        }
        Format::PrqlReferences => {
            let std_lib = load_std_lib()?;
            let (_, context) = semantic::analyze(std_lib, None)?;

            let query = parse(source)?;
            let (nodes, context) = semantic::analyze(query.nodes, Some(context))?;

            semantic::label_references(&nodes, &context, "".to_string(), source.to_string());

            format!("{context:?}").as_bytes().to_vec()
        }
        Format::PrqlFrames => {
            let query = parse(source)?;

            // resolve
            let std_lib = load_std_lib()?;
            let (_, context) = semantic::analyze(std_lib, None)?;
            let (nodes, context) = semantic::analyze(query.nodes, Some(context))?;

            let frames = semantic::collect_frames(nodes);

            // combine with source
            combine_prql_and_frames(source, frames, context)
                .as_bytes()
                .to_vec()
        }
        Format::Sql => {
            let query = parse(source)?;
            let sql = resolve_and_translate(query)?;

            sql.as_bytes().to_vec()
        }
    })
}

fn combine_prql_and_frames(source: &str, frames: Vec<(Span, Frame)>, context: Context) -> String {
    let source = Source::from(source);
    let lines = source.lines().collect_vec();
    let width = lines.iter().map(|l| l.len()).max().unwrap_or(0);

    let mut printed_lines = 0;
    let mut result = Vec::new();
    for (span, frame) in frames {
        let line = source.get_line_range(&Range::from(span)).start;

        while printed_lines < line {
            result.push(lines[printed_lines].chars().collect());
            printed_lines += 1;
        }

        let chars: String = lines[printed_lines].chars().collect();
        printed_lines += 1;

        let cols = frame
            .get_column_names(&context)
            .into_iter()
            .map(|c| c.unwrap_or_else(|| "?".to_string()))
            .join(", ");
        result.push(format!("{chars:width$} # [{cols}]"));
    }

    result.into_iter().join("\n")
}

#[cfg(test)]
mod tests {
    use insta::assert_snapshot;

    use super::*;

    #[test]
    fn prql_layouts_test() {
        let output = compile_to(
            Format::PrqlFrames,
            r#"
from initial_table
select [first = name, last = last_name, gender]
derive full_name = first + " " + last
take 23
select [last + " " + first, full = full_name, gender]
sort full
        "#,
        )
        .unwrap();
        assert_snapshot!(String::from_utf8(output).unwrap().trim(),
        @r###"
        from initial_table                                     # [initial_table.*]
        select [first = name, last = last_name, gender]        # [first, last, gender]
        derive full_name = first + " " + last                  # [first, last, gender, full_name]
        take 23                                                # [first, last, gender, full_name]
        select [last + " " + first, full = full_name, gender]  # [?, full, gender]
        sort full                                              # [?, full, gender]
        "###);
    }
}
