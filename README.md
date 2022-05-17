# PRQL

<!-- User badges on first line (language docs & chat) -->
[![Language Docs](https://img.shields.io/badge/DOCS-LANGUAGE-blue?style=for-the-badge)](https://lang.prql.builders)
[![Discord](https://img.shields.io/discord/936728116712316989?label=discord%20chat&style=for-the-badge)](https://discord.gg/eQcfaCmsNc)
[![VSCode](https://img.shields.io/visual-studio-marketplace/v/prql.prql?label=vscode&style=for-the-badge)](https://marketplace.visualstudio.com/items?itemName=prql.prql)
<!-- Dev badges on first line (language docs & chat) -->
[![Rust API Docs](https://img.shields.io/badge/DOCS-RUST-brightgreen?style=for-the-badge&logo=rust)](https://docs.rs/prql/)
[![GitHub CI Status](https://img.shields.io/github/workflow/status/prql/prql/tests?logo=github&style=for-the-badge)](https://github.com/prql/prql/actions?query=workflow:tests)
[![GitHub contributors](https://img.shields.io/github/contributors/prql/prql?style=for-the-badge)](https://github.com/prql/prql/graphs/contributors)
[![Stars](https://img.shields.io/github/stars/prql/prql?style=for-the-badge)](https://github.com/prql/prql/stargazers)

**P**ipelined **R**elational **Q**uery **L**anguage, pronounced "Prequel".

PRQL is a modern language for transforming data — a simpler and more powerful
SQL. Like SQL, it's readable, explicit and declarative. Unlike SQL, it forms a
logical pipeline of transformations, and supports abstractions such as variables
and functions. It can be used with any database that uses SQL, since it
transpiles to SQL.

PRQL was discussed on [Hacker
News](https://news.ycombinator.com/item?id=30060784#30062329) and
[Lobsters](https://lobste.rs/s/oavgcx/prql_simpler_more_powerful_sql) earlier
this year when it was just a proposal.

<!-- this document is intended for developers and contributors of the language -->
## Contributing

If you're interested in joining the community to build a better SQL, there are
lots of ways of contributing; big and small:

- Star this repo.
- Send a link to PRQL to a couple of people whose opinion you respect.
- Subscribe to [Issue #1](https://github.com/prql/prql/issues/1) for
  updates.
- Join the [Discord](https://discord.gg/eQcfaCmsNc).
- Contribute towards the code. There are many ways of contributing, for any
  level of experience with rust. And if you have rust questions, there are lots of
  friendly people on the Discord who will patiently help you.
  - Find an issue labeled [help
    wanted](https://github.com/prql/prql/issues?q=is%3Aissue+is%3Aopen+label%3A%22help+wanted%22)
    or [good first
    issue](https://github.com/prql/prql/issues?q=is%3Aissue+is%3Aopen+label%3A%22good+first+issue%22)
    and try to fix it. Feel free to PR partial solutions, or ask any questions on
    the Issue or Discord.
  - Start with something tiny! Write a test / write a docstring / make some rust
    nicer — it's a great way to get started in 30 minutes.
- Contribute towards the language.
  - Find instances where the compiler produces incorrect results, and post a bug
    report — feel free to use the [online
    compiler](https://lang.prql.builders/editor).
  - Open an issue / append to an existing issue with examples of queries that
    are difficult to express in PRQL — especially if more difficult than SQL.
  - With sufficient examples, suggest a change to the language! (Though
    suggestions *without* examples are difficult to engage with, so please do
    anchor suggestions in examples.)

Any of these will inspire others to invest their time and energy into the
project; thank you in advance.

### Development environment

Setting up a local dev environment is simple, thanks to the rust ecosystem:

- Install [`rustup` & `cargo`](https://doc.rust-lang.org/cargo/getting-started/installation.html).
- That's it! Running `cargo test` should complete successfully.
- For more advanced development; e.g. adjusting `insta` outputs or compiling for
  web, run the commands in [Taskfile.yml](Taskfile.yml), either by copying &
  pasting or by installing [Task](https://taskfile.dev/#/installation) and
  running `task setup-dev`.
- For quick contributions, hit `.` in GitHub to launch a [github.dev
  instance](https://github.dev/prql/prql).
- Any problems: post an issue and we'll help.

### Contributors

Many thanks to those who've made our progress possible:

[![Contributors](https://contrib.rocks/image?repo=prql/prql)](https://github.com/prql/prql/graphs/contributors)

### Core developers

We have a few core developers who are responsible for reviewing code, making
decisions on the direction of the language, and project administration:

- [**@aljazerzen**](https://github.com/aljazerzen) — Aljaž Mur Eržen
- [**@max-sixty**](https://github.com/max-sixty) — Maximilian Roos
- [**@charlie-sanders**](https://github.com/charlie-sanders) — Charlie Sanders

We welcome others to join who have a track record of contributions.

## Inspired by

- [dplyr](https://dplyr.tidyverse.org/) is a beautiful language for manipulating
  data, in R. It's very similar to PRQL. It only works on in-memory R data.
  - There's also [dbplyr](https://dbplyr.tidyverse.org/) which compiles a subset
    of dplyr to SQL, though requires an R runtime.
- [Kusto](https://docs.microsoft.com/azure/data-explorer/kusto/query/samples?pivots=azuredataexplorer)
  is also a beautiful pipelined language, very similar to PRQL. But it can only
  use Kusto-compatible DBs.
  - A Kusto-to-SQL transpiler would be a legitimate alternative to PRQL, though
     there would be some impedance mismatch in some areas. My central criticism
     of Kusto is that it gives up broad compatibility without getting that much
     in return.
- [Against SQL](https://www.scattered-thoughts.net/writing/against-sql/) gives a
  fairly complete description of SQL's weaknesses, both for analytical and
  transactional queries. [**@jamii**](https://github.com/jamii) consistently
  writes insightful pieces, and it's worth sponsoring him for his updates.
- Julia's [DataPipes.jl](https://gitlab.com/aplavin/DataPipes.jl) &
  [Chain.jl](https://github.com/jkrumbiegel/Chain.jl), which demonstrate how
  effective point-free pipelines can be, and how line-breaks can work as pipes.
- [OCaml](https://ocaml.org/), for its elegant and simple syntax.

## Similar projects

- [Ecto](https://hexdocs.pm/ecto/Ecto.html#module-query) is a sophisticated
  ORM library in Elixir which has pipelined queries as well as more traditional
  ORM features.
- [Morel](http://blog.hydromatic.net/2020/02/25/morel-a-functional-language-for-data.html)
  is a functional language for data, also with a pipeline concept. It doesn't
  compile to SQL but states that it can access external data.
- [Malloy](https://github.com/looker-open-source/malloy) from Looker &
  [**@lloydtabb**](https://github.com/lloydtabb) in a new language which
  combines a declarative syntax for querying with a modelling layer.
- [FunSQL.jl](https://github.com/MechanicalRabbit/FunSQL.jl) is a library in
  Julia which compiles a nice query syntax to SQL. It requires a Julia runtime.
- [LINQ](https://docs.microsoft.com/dotnet/csharp/linq/write-linq-queries),
  is a pipelined language for the `.NET` ecosystem which can (mostly) compile to
  SQL. It was one of the first languages to take this approach.
- [Sift](https://github.com/RCHowell/Sift) is an experimental language which
  heavily uses pipes and relational algebra.
- After writing this proposal (including the name!), I found
  [Preql](https://github.com/erezsh/Preql). Despite the similar name and
  compiling to SQL, it seems to focus more on making the language python-like,
  which is very different to this proposal.

> If any of these descriptions can be improved, please feel free to PR changes.
