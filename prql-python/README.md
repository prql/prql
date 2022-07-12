# prql-python

`prql-python` offers rust bindings to the `prql-compiler` rust library. It
exposes a python method `to_sql(query: str) -> str`.

This is consumed by [PyPrql](https://github.com/prql/PyPrql) &
[dbt-prql](https://github.com/prql/dbt-prql).

The crate is not published to crates.io; only to PyPI.

## Installation

`pip install prql-python`

## Usage

```python
import prql_python as prql

prql_query = """
    from employees
    join salaries [emp_id]
    group [dept_id, gender] (
      aggregate [
        avg_salary = average salary
      ]
    )
"""

sql = prql.to_sql(prql_query)
```

Relies on [pyo3](https://github.com/PyO3/pyo3) for all the magic.

```rust
#[pyfunction]
pub fn to_sql(query: &str) -> PyResult<String> {}
fn prql_python(_py: Python, m: &PyModule) -> PyResult<()> {}
```
