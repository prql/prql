// All copied from `mdbook_preprocessor_boilerplate` apart from the function
// which does the replacement.
// This file is licensed under GPL-3.0 then. We don't link against it from PRQL.
use anyhow::{bail, Result};
use clap::{Arg, ArgMatches, Command};
use mdbook::preprocess::PreprocessorContext;
use mdbook::preprocess::{CmdPreprocessor, Preprocessor};
use mdbook::{book::Book, BookItem};
use prql_compiler::compile;
use pulldown_cmark::{CodeBlockKind, Event, Options, Parser, Tag};
use pulldown_cmark_to_cmark::cmark;
use semver::{Version, VersionReq};
use similar::DiffableStr;
use std::{io, process};

/// Checks renderer support and runs the preprocessor.
pub fn run(preprocessor: impl Preprocessor, description: &str) {
    let matches = Command::new(preprocessor.name())
        .about(description)
        .subcommand(
            Command::new("supports")
                .arg(Arg::new("renderer").required(true))
                .about("Check whether a renderer is supported by this preprocessor"),
        )
        .get_matches();

    if let Some(sub_args) = matches.subcommand_matches("supports") {
        handle_supports(preprocessor, sub_args);
    } else if let Err(e) = handle_preprocessing(preprocessor) {
        eprintln!("{}", e);
        process::exit(1);
    }
}

fn handle_preprocessing(pre: impl Preprocessor) -> Result<()> {
    let (ctx, book) = CmdPreprocessor::parse_input(io::stdin())?;

    let book_version = Version::parse(&ctx.mdbook_version)?;
    let version_req = VersionReq::parse(mdbook::MDBOOK_VERSION)?;

    if !version_req.matches(&book_version) {
        eprintln!(
            "Warning: The {} plugin was built against version {} of mdbook, \
             but we're being called from version {}",
            pre.name(),
            mdbook::MDBOOK_VERSION,
            ctx.mdbook_version
        );
    }

    let processed_book = pre.run(&ctx, book)?;
    let out = serde_json::to_string(&processed_book)?;
    println!("{}", out);

    Ok(())
}

fn handle_supports(pre: impl Preprocessor, sub_args: &ArgMatches) -> ! {
    let renderer = sub_args.value_of("renderer").expect("Required argument");
    let supported = pre.supports_renderer(renderer);

    // Signal whether the renderer is supported by exiting with 1 or 0.
    if supported {
        process::exit(0);
    } else {
        process::exit(1);
    }
}

fn main() {
    eprintln!("Running comparison preprocessor");
    run(
        ComparisonPreprocessor,
        "Create comparison examples between PRQL & SQL",
    );
}

struct ComparisonPreprocessor;

impl Preprocessor for ComparisonPreprocessor {
    fn name(&self) -> &str {
        "comparison-preprocessor"
    }

    fn run(&self, _ctx: &PreprocessorContext, mut book: Book) -> Result<Book> {
        eprintln!("Running comparison preprocessor");
        book.for_each_mut(|item: &mut BookItem| {
            if let BookItem::Chapter(chapter) = item {
                let new = replace_examples(&chapter.content).unwrap();
                chapter.content.clear();
                chapter.content.push_str(&new);
            }
        });

        Ok(book)
    }

    fn supports_renderer(&self, renderer: &str) -> bool {
        renderer == "html"
    }
}

fn replace_examples(text: &str) -> Result<String> {
    let mut parser = Parser::new_ext(text, Options::all());
    let mut cmark_acc = vec![];

    while let Some(event) = parser.next() {
        match event.clone() {
            Event::Start(Tag::CodeBlock(CodeBlockKind::Fenced(lang))) if lang == "prql".into() => {
                if let Some(Event::Text(text)) = parser.next() {
                    let prql = text.to_string();
                    let html = table_of_comparison(text.as_str().unwrap(), &compile(&prql)?);
                    cmark_acc.push(Event::Html(html.into()));

                    // Skip ending tag
                    parser.next();
                } else {
                    bail!("Expected text after PRQL code block");
                }
            }
            _ => cmark_acc.push(event.to_owned()),
        }
    }
    let mut buf = String::new();
    cmark(cmark_acc.into_iter(), &mut buf)?;

    Ok(buf)
}

fn table_of_comparison(prql: &str, sql: &str) -> String {
    format!(
        r#"
<div class="comparison">

<div>
<h4>PRQL</h4>

```prql
{prql}
```

</div>

<div>
<h4>SQL</h4>

```sql
{sql}
```

</div>

</div>
"#,
        prql = prql.trim(),
        sql = sql,
    )
    .trim_start()
    .to_string()
}

#[test]
fn test_table() -> Result<()> {
    use insta::assert_display_snapshot;
    let table = r###"
# Syntax

| a |
|---|
| c |


| a   |
|-----|
| \|  |

"###;

    assert_display_snapshot!(replace_examples(table)?, @r###"
    # Syntax

    |a|
    |-|
    |c|

    |a|
    |-|
    |\||
    "###);

    Ok(())
}
