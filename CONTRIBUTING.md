# Contributing

If you're interested in joining the community to build a better SQL, there are
lots of ways of contributing; big and small:

- Star this repo.
- Send a link to PRQL to a couple of people whose opinion you respect.
- Subscribe to [Issue #1](https://github.com/prql/prql/issues/1) for
  updates.
- Join the [Discord](https://discord.gg/eQcfaCmsNc).
- Contribute towards the code. Most of the code is written in rust, and there's
  enough to do such that any level of experience with rust is sufficient. And if
  you have rust questions, there are lots of friendly people on the Discord who
  will patiently help you.
  - Find an issue labeled [help
    wanted](https://github.com/prql/prql/issues?q=is%3Aissue+is%3Aopen+label%3A%22help+wanted%22)
    or [good first
    issue](https://github.com/prql/prql/issues?q=is%3Aissue+is%3Aopen+label%3A%22good+first+issue%22)
    and try to fix it. Feel free to PR partial solutions, or ask any questions on
    the Issue or Discord.
  - Start with something tiny! Write a test / write a docstring / make some rust
    nicer — it's a great way to get started by making an lasting impact in 30 minutes.
- Contribute towards the language.
  - Find instances where the compiler produces incorrect results, and post a bug
    report — feel free to use the [playground](https://prql-lang.org/playground).
  - Open an issue / append to an existing issue with examples of queries that
    are difficult to express in PRQL — especially if more difficult than SQL.
  - With sufficient examples, suggest a change to the language! (Though
    suggestions _without_ examples are difficult to engage with, so please do
    anchor suggestions in examples.)
- Contribute towards the project.
  - Improve our website / book.
  - Tell people about PRQL.
  - Find a group of users who would be interested in PRQL, help them get up to
    speed, help the project understand what they need.

Any of these will inspire others to invest their time and energy into the
project; thank you in advance.

## Development environment

Setting up a local dev environment is simple, thanks to the rust ecosystem:

- Install [`rustup` & `cargo`](https://doc.rust-lang.org/cargo/getting-started/installation.html).
- That's it! Running `cargo test` should complete successfully.
- For more advanced development; e.g. adjusting `insta` outputs or compiling for
  web, run `task setup-dev` by installing
  [Task](https://taskfile.dev/#/installation), or by copying & pasting them from
  [Taskfile.yml](Taskfile.yml).
- For quick contributions, hit `.` in GitHub to launch a [github.dev
  instance](https://github.dev/prql/prql).
- Any problems: post an issue and we'll help.

## Merging

- **We merge any code that makes PRQL better**
- A PR doesn't need to be perfect to be merged; it doesn't need to solve a big
  problem. It needs to:
  - be in the right direction
  - make incremental progress
  - be explicit on its current state, so others can continue the progress
- If you have merge permissions, and are reasonably confident that a PR is
  suitable to merge (whether or not you're the author), feel free to merge.
  - If you don't have merge permissions and have authored a few PRs, ask and ye
    shall receive.
- The primary way we ratchet the code quality is through automated tests.
  - This means PRs almost always need a test to demonstrate incremental
    progress.
  - If a change breaks functionality without breaking tests, our tests were
    insufficient.
- We use PR reviews to give general context, offer specific assistance, and
  collaborate on larger decisions.
  - Reviews around 'nits' like code formatting / idioms / etc are very welcome.
    But the norm is for them to be received as helpful advice, rather than as
    mandatory tasks to complete. Adding automated tests & lints to automate
    these suggestions is welcome.
  - If you have merge permissions and would like a PR to be reviewed before it
    merges, that's great — ask or assign a reviewer.
  - If a PR hasn't received attention after a day, please feel free to ping the
    pull request.
- People may review a PR after it's merged. As part of the understanding that we
  can merge quickly, contributors are expected to incorporate this feedback into
  a future PR.
- We should revert quickly if the impact of a PR turns out not to be consistent
  with our expectations, or there isn't as much consensus on a decision as we
  had hoped. It's very easy to revert code and then re-revert when we've
  resolved the issue; it's a sign of moving quickly.

## Tasks

We have a couple of tasks which incorporate all building & testing. While they
don't need to be run as part of a standard dev loop — generally we'll want to
run a more specific test — they can be useful as a backstop to ensure everything
works, and as a reference for how each part of the repo is built & tested. They
should be broadly consistent with the GitHub Actions workflows; please report
any inconsistencies.

To build everything:

```sh
task build-all
```

To run all tests; (which includes building everything):

```sh
task test-all
```

These require installing Task, either `brew install go-task/tap/go-task` or
as described on [Task](https://taskfile.dev/#/installation).

## Tests

We use a pyramid of tests — we have fast, focused tests at the bottom of the
pyramid, which give us low latency feedback when developing, and then slower,
broader tests which ensure that we don't miss anything as PRQL develops[^2].

> If you're making your first contribution, you don't need to engage with all this
> — it's fine to just make a change and push the results; the tests that run in
> GitHub will point you towards any errors, which can be then be run locally if
> needed. We're always around to help out.

Our tests:

- **[Static checks](.pre-commit-config.yaml)** — we run a few static checks to
  ensure the code stays healthy and consistent. They're defined in
  [**`.pre-commit-config.yaml`**](.pre-commit-config.yaml), using
  [pre-commit](https://pre-commit.com). They can be run locally with

  ```sh
  pre-commit run -a
  ```

  The tests fix most of the issues they find themselves. Most of them also run
  on GitHub on every commit; any changes they make are added onto the branch
  automatically in an additional commit.

- **Unit tests & inline insta snapshots** — like most projects, we rely on
  unit tests to test that our code basically works. We extensively use
  [Insta](https://insta.rs/), a snapshot testing tool which writes out the
  results of an expression in our code, making it faster to write and modify
  tests[^4].

  These are the fastest tests which run our code; they're designed to run on
  every save while you're developing. (While they're covered by `task test-all`,
  you'll generally want to have lower-latency tests running in a tight loop.).[^3]

- **[Integration
  tests](https://github.com/prql/prql/blob/main/prql-compiler/tests/integration/README.md)**
  — these run tests against real databases, to ensure we're producing correct
  SQL.

- **[Examples](https://github.com/prql/prql/blob/main/book/tests/snapshot.rs)**
  — we compile all examples in the PRQL Book, to test that they produce the SQL
  we expect, and that changes to our code don't cause any unexpected
  regressions.

- **[GitHub Actions on every
  commit](https://github.com/prql/prql/blob/main/.github/workflows/pull-request.yaml)**
  — we run tests on `prql-compiler` for standard & wasm targets, and the
  examples in the book on every pull request every time a commit is pushed.
  These are designed to run in under one minute, and we should be reassessing
  their scope if they grow beyond that. Once these pass, a pull request can be
  merged.

  All tests up to this point can be run with `task test-all` locally.

- **[GitHub Actions on specific
  changes](https://github.com/prql/prql/blob/main/.github/workflows/test-all.yaml)**
  — we run additional tests on pull requests when we identify changes to some
  paths, such as bindings to other languages.

- **[GitHub Actions on
  merge](https://github.com/prql/prql/tree/main/.github/workflows)** — we run
  many more tests on every merge to main. This includes testing across OSs, all
  our language bindings, our `task` tasks, a measure of test code coverage, and
  some performance benchmarks.

  We can run these tests before a merge by adding a label `pr-test-all` to the
  PR.

  If these tests fail after merging, we revert the merged commit before fixing the test and
  then re-reverting.

The goal of our tests is to allow us to make changes quickly. If you find
they're making it more difficult for you to make changes, or there are missing
tests that would give you the confidence to make changes faster, then please
raise an issue.

[^1]:
    We don't want to re-run on _any_ file changing, because we can get into a
    loop of writing snapshot files, triggering a change, writing a snapshot
    file, etc.

[^2]:
    Our approach is very consistent with
    **[@matklad](https://github.com/matklad)**'s advice, in his excellent blog
    post [How to Test](https://matklad.github.io//2021/05/31/how-to-test.html).

[^3]: For example, this is a command I frequently run:

    ```sh
    RUST_BACKTRACE=1 watchexec -e rs,toml,pest,md -cr -- cargo insta test --accept -- -p prql-compiler --lib
    ```

    Breaking this down:

    - `RUST_BACKTRACE=1` will print a full backtrace, including where an error
      value was created, for rust tests which return `Result`s.
    - `watchexec -e rs,toml,pest,md -cr --` will run the subsequent command on any
      change to files with extensions which we are generally editing[^1].
    - `cargo insta test --accept --` runs tests with `insta`, a snapshot library, and
      writes any results immediately. I rely on git to track changes, so I run
      with `--accept`, but YMMV.
    - `-p prql-compiler --lib` is passed to cargo by `insta`; `-p prql-compiler`
      tells it to only run the tests for `prql-compiler` rather than the other
      crates, and `--lib` to only run the unit tests rather than the integration
      tests, which are much slower.

[^4]:
    [Here's an example of an insta
    test](https://github.com/prql/prql/blob/0.2.2/prql-compiler/src/parser.rs#L580-L605)
    — note that only the initial line of each test is written by us; the remainder
    is filled in by insta. .
