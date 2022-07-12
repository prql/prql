# PRQL test-databases

Test PRQL queries against various SQL RDBMS.

## Data

Database chinook.db was downloaded from <https://www.sqlitetutorial.net/sqlite-sample-database>

Columns are renamed to snake_case, so Postgres and DuckDb don't struggle with them.

For optimal accessability, portability between databases and file size, all tables are stored
as CSV files. Their current size is 432kB, it could be gzip-ed to 112kB, but that would require a preprocessing step before running `cargo test`.

## SQLite

Can be run as part of `cargo test`. Uses bundled sqlite, compiled as part of cargo build.

## DuckDb

Can be run as part of `cargo test`. Uses bundled DuckDb, compiled as part of cargo build.

## Postgres

If passed environmental variable `POSTGRES_HOST` this crate will requests postgres server that
should already have data loaded in.

### Docker compose

There is also a proof on concept for testing done against Postgres, which can
be run by running `docker-compose up`. This will:

- build a docker image for Postgres (with data already loaded in)
- build a docker image for this crate (+data), compiled with --tests
- run the two images, executing the tests.

## Test organization

We follow the advice in
<https://matklad.github.io/2021/02/27/delete-cargo-integration-tests.html>.
