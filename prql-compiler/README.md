# PRQL compiler

`prql-compiler` contains the implementation of PRQL's compiler, written in rust.

For more on PRQL, check out the [PRQL website](https://prql-lang.org) or the [PRQL
repo](https://github.com/prql/prql).

## Installation

`prql-compiler` can be installed with `cargo`:

```sh
cargo install prql-compiler
```

...or built from source:

```sh
# from prql/prql-compiler
cargo install --path .
```

It can be installed via brew too:

```sh
brew install prql/prql/prql-compiler
```

## Usage

```sh
$ echo "from employees | filter has_dog | select salary" | prql-compiler compile

SELECT
  *
FROM
  employees
WHERE
  has_dog
```
