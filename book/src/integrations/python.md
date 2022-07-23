# Python (prql-python)

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
