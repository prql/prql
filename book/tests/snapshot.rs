#![cfg(not(target_family = "wasm"))]
/// This test:
/// - Extracts PRQL code blocks into the `examples` path.
/// - Converts them to SQL using insta, raising an error if there's a diff.
/// - Replaces the PRQL code block with a comparison table.
//
// Overall, this is overengineered — it's complicated and took a long time to
// write. The intention is good — have a version of the SQL that's committed
// into the repo, and join our tests with our docs. But it feels like overly
// custom code for quite a general problem, even if our preferences are slightly
// different from the general case.
//
// Possibly we should be using something like pandoc /
// https://github.com/gpoore/codebraid / which would run the transformation for
// us. They introduce a bunch of non-rust dependencies, which is not ideal, but
// passable. They don't let us customize our formatting (e.g. in a table).
//
use anyhow::{bail, Result};
use globset::Glob;
use insta::{assert_snapshot, glob};
use log::warn;
use prql_compiler::*;
use pulldown_cmark::{CodeBlockKind, Event, Parser, Tag};
use std::fs;
use std::path::Path;
use walkdir::WalkDir;

#[test]
fn run_examples() -> Result<()> {
    // TODO: This doesn't delete old prql files — probably we should delete them
    // all first?
    //
    // TODO: In CI this could pass by replacing files that are wrong in the
    // repo; instead we could check if there are any diffs after this has run?

    // Note that on windows, we only get the next _line_, and so we exclude the
    // writing on Windows. ref https://github.com/prql/prql/issues/356
    #[cfg(not(target_family = "windows"))]
    write_reference_prql()?;
    run_reference_prql()?;

    Ok(())
}

/// Extract reference examples from the PRQL docs and write them to the
/// `tests/prql` path, one in each file.
// We could alternatively have used something like
// https://github.com/earldouglas/codedown, but it's not much code, and it
// requires no dependencies.
//
// We allow dead_code because of the window issue described above. (Can we allow
// it only for windows?)
#[allow(dead_code)]
fn write_reference_prql() -> Result<()> {
    // Remove old .prql files, since we're going to rewrite them, and we don't want
    // old files which wouldn't be rewritten from hanging around.
    // We use `trash`, since we don't want to be removing files with test code
    // in case there's a bug.

    let examples_path = Path::new("tests/prql");
    if examples_path.exists() {
        trash::delete(Path::new("tests/prql")).unwrap_or_else(|e| {
            warn!("Failed to delete old examples: {}", e);
        });
    }

    let glob = Glob::new("**/*.md")?.compile_matcher();

    WalkDir::new(Path::new("./src/"))
        .into_iter()
        .flatten()
        .filter(|x| glob.is_match(x.path()))
        .try_for_each(|dir_entry| {
            let text = fs::read_to_string(dir_entry.path())?;
            let mut parser = Parser::new(&text);
            let mut prql_blocks = vec![];
            while let Some(event) = parser.next() {
                match event.clone() {
                    // At the start of a PRQL code block, push the _next_ item.
                    // Note that on windows, we only get the next _line_, and so
                    // we exclude the writing in windows. TODO: iterate over the
                    // lines so this works on windows; https://github.com/prql/prql/issues/356
                    Event::Start(Tag::CodeBlock(CodeBlockKind::Fenced(lang)))
                        if lang == "prql".into() =>
                    {
                        if let Some(Event::Text(text)) = parser.next() {
                            prql_blocks.push(text);
                        } else {
                            bail!("Expected text after PRQL code block");
                        }
                    }
                    _ => {}
                }
            }

            // Write each one to a new file.
            prql_blocks
                .iter()
                .enumerate()
                .try_for_each(|(i, example)| {
                    let file_relative = &dir_entry
                        .path()
                        .strip_prefix("./src/")?
                        .to_str()
                        .unwrap()
                        .trim_end_matches(".md");
                    let prql_path = format!("tests/prql/{file_relative}-{i}.prql");

                    fs::create_dir_all(Path::new(&prql_path).parent().unwrap())?;
                    fs::write(prql_path, example.to_string())?;

                    Ok::<(), anyhow::Error>(())
                })?;
            Ok(())
        })?;

    Ok(())
}

/// Snapshot the output of each example.
fn run_reference_prql() -> Result<()> {
    glob!("prql/**/*.prql", |path| {
        let prql = fs::read_to_string(path).unwrap();

        if prql.contains("skip_test") {
            return;
        }

        let sql = compile(&prql).unwrap_or_else(|e| format!("Failed to compile `{prql}`; {e}"));
        assert_snapshot!(sql);
    });
    Ok(())
}
