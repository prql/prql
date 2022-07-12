# Select

Picks and computes columns.

```prql_no_test
select [{assign_expression}]
```

## Examples

```prql
from employees
select first_name
```

```prql
from employees
select [first_name, last_name]
```

```prql
from employees
select name = f"{first_name} {last_name}"
```

```prql
from employees
select [
  name = f"{first_name} {last_name}",
  age_eoy = dob - @2022-12-31,
]
```
