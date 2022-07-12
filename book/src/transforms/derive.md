# Derive

Computes one or more new columns.

```prql_no_test
derive [{new_name} = {expression}]
```

## Examples

```prql
from employees
derive gross_salary = salary + payroll_tax
```

```prql
from employees
derive [
  gross_salary = salary + payroll_tax,
  gross_cost = gross_salary + benefits_cost
]
```

`derive` generally computes a column from existing columns, but can also take a
literal in which case it can begin a pipeline without a `from`:

```prql
derive x = 5
```
