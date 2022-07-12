---
title: "Examples"
---

## A simple example

Here's a fairly simple SQL query:

```sql
SELECT TOP 20
  title,
  country,
  AVG(salary) AS average_salary,
  SUM(salary) AS sum_salary,
  AVG(salary + payroll_tax) AS average_gross_salary,
  SUM(salary + payroll_tax) AS sum_gross_salary,
  AVG(salary + payroll_tax + benefits_cost) AS average_gross_cost,
  SUM(salary + payroll_tax + benefits_cost) AS sum_gross_cost,
  COUNT(*) AS ct
FROM
  employees
WHERE
  start_date > DATE('2021-01-01')
  AND salary + payroll_tax + benefits_cost > 0
GROUP BY
  title,
  country
HAVING
  COUNT(*) > 200
ORDER BY
  sum_gross_cost,
  country DESC
```

Even this simple query demonstrates some of the problems with SQL's lack of
abstractions:

- Unnecessary repetition — the calculations for each measure are repeated,
  despite deriving from a previous measure. The repetition in the `WHERE`
  clause obfuscates the meaning of the expression.
- Functions have multiple operators — `HAVING` & `WHERE` are fundamentally
  similar operations applied at different stages of the pipeline, but SQL's lack
  of pipeline-based precedence requires it to have two different operators.
- Operators have multiple functions — the `SELECT` operator both
  creates new aggregations, and selects which columns to include.
- Awkward syntax — when developing the query, commenting out the final line of
  the `SELECT` list causes a syntax error because of how commas are handled, and
  we need to repeat the columns in the `GROUP BY` clause in the `SELECT` list.

Here's the same query with PRQL:

```prql
from employees                                # Each line transforms the previous result.
filter start_date > @2021-01-01               # Clear date syntax.
derive [                                      # `derive` adds columns / variables.
  gross_salary = salary + payroll_tax,
  gross_cost = gross_salary + benefits_cost   # Variables can use other variables.
]
filter gross_cost > 0
group [title, country] (                      # `group` runs a pipeline over each group.
  aggregate [                                 # `aggregate` reduces a column to a row.
    average salary,
    sum     salary,
    average gross_salary,
    sum     gross_salary,
    average gross_cost,
    sum_gross_cost = sum gross_cost,          # `=` sets a column name.
    ct = count,
  ]
)
sort [sum_gross_cost, -country]               # `-country` means descending order.
filter ct > 200
take 20
```

As well as using variables to reduce unnecessary repetition, the query is also
more readable — it flows from top to bottom, each line representing a
transformation of the previous line's result. For example, `TOP 20` / `take 20`
modify the final result in both queries — but only PRQL represents it as the
final transformation. And context is localized — the `aggregate` transform is
immediately wrapped in a `group` transform containing the columns to group by.

While PRQL is designed for reading & writing by people, it's also much simpler
for code to construct or edit PRQL queries. In SQL, adding a filter to a query
involves parsing the query to find and then modify the `WHERE` statement, or
wrapping the existing query in a CTE. In PRQL, adding a filter just involves
appending a `filter` transformation to the query.

For more examples, check out the [PRQL Book](https://prql-lang.org/book/).

<!--

TODO: This was a nice example for the proposal, but until we get functions which can contain column names,
it doesn't compile, and so is confusing. When we get that working, we can re-enable it.

## A more complex example

Here's another SQL query, which calculates returns from prices on days with
valid prices.

> The implemented version of PRQL supports some but not all these features.

```sql
WITH total_returns AS (
  SELECT
    date,
    sec_id,
    -- Can't use a `WHERE` clause, as it would affect the row that the `LAG` function referenced.
    IF(is_valid_price, price_adjusted / LAG(price_adjusted, 1) OVER
      (PARTITION BY sec_id ORDER BY date) - 1 + dividend_return, NULL) AS return_total,
    IF(is_valid_price, price_adjusted_usd / LAG(price_adjusted_usd, 1) OVER
      (PARTITION BY sec_id ORDER BY date) - 1 + dividend_return, NULL) AS return_usd,
    IF(is_valid_price, price_adjusted / LAG(price_adjusted, 1) OVER
      (PARTITION BY sec_id ORDER BY date) - 1 + dividend_return, NULL)
      - interest_rate / 252 AS return_excess,
    IF(is_valid_price, price_adjusted_usd / LAG(price_adjusted_usd, 1) OVER
      (PARTITION BY sec_id ORDER BY date) - 1 + dividend_return, NULL)
      - interest_rate / 252 AS return_usd_excess
  FROM prices
)
SELECT
  *,
  return_total - (interest_rate / 252) AS return_excess,
  EXP(SUM(LN(GREATEST(1 + return_total - (interest_rate / 252), 0.01))) OVER (ORDER BY date)) AS return_excess_index
FROM total_returns
JOIN interest_rates USING (date)
```

> This might seem like a convoluted example, but it's taken from a real query.
> Indeed, it's also simpler and smaller than the full logic — note that it
> starts from `price_adjusted`, whose logic had to be split into a previous
> query to avoid the SQL becoming even less readable.

Here's the same query with PRQL:

```prql
prql version:0.3 db:snowflake                         # PRQL version & database name.

func excess x -> (x - interest_rate) / 252            # Functions are clean and simple.
func if_valid x -> is_valid_price ? x : null
func lag_day x -> group sec_id (                      # `group` is used for window partitions too
  sort date
  window (                                            # `window` runs a pipeline over each window
    lag 1 x                                           # `lag 1 x` lags the `x` col by 1
  )
)

func ret x -> x / (x | lag_day) - 1 + dividend_return

from prices
join interest_rates [date]
select [                                              # `select` only includes unnamed columns, unlike `derive`
  return_total =      prices_adj   | ret | if_valid   # `|` can be used rather than newlines
  return_usd =        prices_usd   | ret | if_valid
  return_excess =     return_total | excess
  return_usd_excess = return_usd   | excess
  return_index = (                                    # No need for a CTE
    return_total + 1
    excess
    greatest 0.01
    ln
    group sec_id (                                    # Complicated logic remains clear(er)
      sort date
      window ..current (                              # Rolling sum
        sum
      )
    )
    exp
  )
]
```

Because we define the functions once rather than copying & pasting the code, we
get all the benefits of encapsulation and extensibility — we have reliable &
tested functions, whose purpose is explicit, which we can share across queries
and between colleagues.

We needed a CTE in the SQL query, because the lack of variables would have
required a nested window clause, which isn't allowed. With PRQL, our logic isn't
constrained by these arbitrary constraints — and is more compressed as a result.

The larger query demonstrates PRQL orthogonality. PRQL has fewer keywords
than SQL, and each of them does something specific and composable; for example:

- `group` maps a pipeline over groups; whether in a table context — `GROUP BY`
  in SQL — or within a `window` — `PARTITION BY` in SQL.
- A transform in context of a `group` does the same transformation to the group
  as it would to the table — for example finding the rolling sum of a column.
  For more on this equivalence, check out [`group`'s
  documentation](https://prql-lang.org/book/transforms/group.html)
- `filter` filters out rows which don't meet a condition. That can be before an
  aggregate — `WHERE` in SQL — after an aggregate — `HAVING` in SQL — or within
  a `window` — `QUALIFY` in SQL. -->
