# S-Strings

An s-string inserts SQL directly, as an escape hatch when there's something that PRQL
doesn't yet implement. For example, there's no `version()` function in SQL that
returns the Postgres version, so if we want to use that, we use an s-string:

```prql
derive db_version = s"version()"
```

We can embed columns in an s-string using braces. For example, PRQL's standard
library defines the `average` function as:

```prql_no_test
func average column -> s"AVG({column})"
```

So this compiles using the function:

```prql
from employees
aggregate [average salary]
```

Here's an example of a more involved use of an s-string:

```prql
from de=dept_emp
join s=salaries side:left [
  (s.emp_no == de.emp_no),
  s"""({s.from_date}, {s.to_date})
  OVERLAPS
  ({de.from_date}, {de.to_date})"""
]
```

For those who have used python, s-strings are similar to python's f-strings, but
the result is SQL, rather than a string literal — a python f-string of
`f"average{col}"` where `col="salary"` would produce `"average(salary)"`, with
the quotes. `s"average{col}"` produces `average(salary)`, without quotes.

s-strings in user code are intended as an escape-hatch for an unimplemented
feature. If we often need s-strings to express something, that's a sign we
should implement it in PRQL or PRQL's stdlib.

## Backticks

PRQL will also pass through identifiers surrounded by backticks (including the
backticks). Some databases — e.g. BigQuery — use this to allow identifiers which
aren't otherwise valid; such as those containing a hyphen.

```prql
from `project-foo.dataset.table`
join `project-bar`.`dataset`.`table` [col_bax]
```
