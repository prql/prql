---
####################### General #########################
layout: home
title: PRQL

####################### Hero section #########################
hero_section:
  enable: true
  heading: "PRQL is a modern language for transforming data"
  bottom_text: "— a simple, powerful, pipelined SQL replacement"
  button:
    enable: false
    link: https://prql-lang.org/book/
    label: "Reference"
  prql_example: |
    from employees
    filter start_date > @2021-01-01
    derive [
      gross_salary = salary + (tax ?? 0),
      gross_cost = gross_salary + benefits_cost,
    ]
    filter gross_cost > 0
    group [title, country] (
      aggregate [
        average gross_salary,
        sum_gross_cost = sum gross_cost,
      ]
    )
    filter sum_gross_cost > 100000
    derive id = f"{title}_{country}"
    sort [sum_gross_cost, -country]
    take 1..20

####################### Principles section #########################
principle_section:
  enable: true
  title: "Principles"
  items:
    - title: "Pipelined"
      main_text: "A PRQL query is a linear pipeline of transformations"
      content:
        Each line of the query is a transformation of the previous line’s result.
        This makes it easy to read, and simple to write.

    - title: "Simple"
      main_text: "PRQL serves both sophisticated engineers and analysts without coding experience."
      content:
        By providing a small number of powerful & orthogonal primitives, queries are simpler —
        there's only one way of expressing each operation. We can eschew the debt that SQL has built up.

    - title: "Open"
      main_text: "PRQL is open-source, with an open community"
      content:
        PRQL will always be fully open-source and will never have a commercial product.
        By compiling to SQL, PRQL is compatible with most databases, existing tools, and programming languages that manage SQL.
        We're a welcoming community for users, contributors, and other projects.

    - title: "Extensible"
      main_text: "PRQL is designed to be extended, from functions to language bindings"
      content: PRQL has abstractions which make it a great platform to build on.
        Its explicit versioning allows changes without breaking backward-compatibility.
        And in the cases where PRQL doesn't yet have an implementation,
        it allows embedding SQL with S-Strings.

    - title: "Analytical"
      main_text: "PRQL's focus is analytical queries"
      content:
        PRQL was originally designed to serve the growing need of writing analytical queries,
        emphasizing data transformations, development speed, and readability.
        We de-emphasize other SQL features such as inserting data or transactions.

showcase_section:
  enable: true
  title: "Showcase"
  content:
    - PRQL consists of a curated set of orthogonal transformations, which are combined together to form a pipeline.
      That makes it easy to compose and extend queries. The language also benefits from modern features, such syntax for dates, ranges and f-strings as well as functions, type checking and better null handling.
  buttons:
    - link: "/playground/"
      label: "Playground"
    - link: "/book/"
      label: "Book"
  examples:
    - id: basics
      label: Basic example
      prql: |
        from employees
        select [id, first_name, age]
        sort age
        take 10
      sql: |
        SELECT id, first_name, age
        FROM employees
        ORDER BY age
        LIMIT 10

    - id: friendly-syntax
      label: Friendly syntax
      prql: |
        from order               # This is a comment
        filter status == "done"
        sort [-amount]           # sort order
      sql: |
        SELECT
          order.*
        FROM
          order
        WHERE
          status = 'done'
        ORDER BY
          amount DESC

    - id: dates
      label: Dates
      prql: |
        from employees
        derive [
          age_at_year_end = (@2022-12-31 - dob),
          first_check_in = start + 10days,
        ]
      sql: |
        SELECT
          employees.*,
          DATE '2022-12-31' - dob AS age_at_year_end,
          start + INTERVAL '10' DAY AS first_check_in
        FROM
          employees

    - id: orthogonal
      label: Orthogonality
      prql: |
        from employees
        # Filter before aggregations
        filter start_date > @2021-01-01
        group country (
          aggregate [max_salary = max salary]
        )
        # And filter after aggregations!
        filter max_salary > 100000
      sql: |
        SELECT
          country,
          MAX(salary) AS max_salary
        FROM
          employees
        WHERE
          start_date > DATE '2021-01-01'
        GROUP BY
          country
        HAVING
          MAX(salary) > 100000

    # markdown-link-check-disable
    - id: f-strings
      label: F-strings
      prql: |
        from web
        # Just like Python
        select url = f"http://www.{domain}.{tld}/{page}"
      sql: |
        SELECT CONCAT('http://www.', domain, '.', tld,
          '/', page) AS url
        FROM web
    # markdown-link-check-enable
    - id: windows
      label: Windows
      prql: |
        from employees
        group employee_id (
          sort month
          window rolling:12 (
            derive [trail_12_m_comp = sum paycheck]
          )
        )
      sql: |
        SELECT
          employees.*,
          SUM(paycheck) OVER (
            PARTITION BY employee_id
            ORDER BY
              month ROWS BETWEEN 11 PRECEDING
              AND CURRENT ROW
          ) AS trail_12_m_comp
        FROM
          employees

    - id: functions
      label: Functions
      prql: |
        func fahrenheit_from_celsius temp -> temp * 9/5 + 32

        from weather
        select temp_f = (fahrenheit_from_celsius temp_c)
      sql: |
        SELECT
          temp_c * 9/5 + 32 AS temp_f
        FROM
          weather

    - id: top-n
      label: Top n items
      prql: |
        # Most recent employee in each role
        # Quite difficult in SQL...
        from employees
        group role (
          sort join_date
          take 1
        )
      sql: |
        WITH table_0 AS (
          SELECT
            employees.*,
            ROW_NUMBER() OVER (
              PARTITION BY role
              ORDER BY
                join_date
            ) AS _rn
          FROM
            employees
        )
        SELECT
          table_0.*
        FROM
          table_0
        WHERE
          _rn <= 1

    - id: s-string
      label: S-strings
      prql: |
        # There's no `version` in PRQL, but
        # we have an escape hatch:
        derive db_version = s"version()"
      sql: |
        SELECT
          version() AS db_version

    - id: joins
      label: Joins
      prql: |
        from employees
        join benefits [employee_id]
        join side:left p=positions [id==employee_id]
        select [employee_id, role, vision_coverage]
      sql: |
        SELECT
          employee_id,
          role,
          vision_coverage
        FROM
          employees
          JOIN benefits USING(employee_id)
          LEFT JOIN positions AS p ON id = employee_id

    - id: null-handling
      label: Null handling
      prql: |
        from users
        filter last_login != null
        filter deleted_at == null
        derive channel = channel ?? "unknown"
      sql: |
        SELECT
          users.*,
          COALESCE(channel, 'unknown') AS channel
        FROM
          users
        WHERE
          last_login IS NOT NULL
          AND deleted_at IS NULL

    - id: dialects
      label: Dialects
      prql: |
        prql dialect:mssql  # Will generate TOP rather than LIMIT

        from employees
        sort age
        take 10
      sql: |
        SELECT
          TOP (10) employees.*
        FROM
          employees
        ORDER BY
          age

tools_section:
  enable: true
  title: "Tools"
  sections:
    - link: https://prql-lang.org/playground/
      label: "Playground"
      text: "Online in-browser playground that compiles PRQL to SQL as you type."

    - link: https://github.com/prql/PyPrql
      label: "PyPrql"
      text: |
        Python TUI for connecting to databases.
        Provides a native interactive console with auto-complete for column names and Jupyter/IPython cell magic.

        `pip install pyprql`

    - link: "https://github.com/prql/prql"
      label: "prql-compiler"
      text: |
        Reference compiler implementation. Has a CLI utility that can transpile, format and annotate PRQL queries.

        `brew install prql/prql/prql-compiler`

integrations_section:
  enable: true
  title: "Integrations"
  sections:
    - label: dbt
      link: https://github.com/prql/dbt-prql
      text: Allows writing PRQL in dbt models.
        This combines the benefits of PRQL's power & simplicity within queries;
        with dbt's version control, lineage & testing across queries.

    - label: "Jupyter/IPython"
      link: https://pyprql.readthedocs.io/en/latest/magic_readme.html
      text:
        "PyPrql contains a Jupyter extension, which executes a PRQL cell against a database.
        It can also set up an in-memory DuckDB instance, populated with a pandas DataFrame."

    - label: Visual Studio Code
      link: https://marketplace.visualstudio.com/items?itemName=prql.prql
      text: Extension with syntax highlighting and an upcoming language server.

    - label: "Prefect"
      link: https://prql-lang.org/book/integrations/prefect.html
      text: Add PRQL models to your Prefect workflows with a single function.

bindings_section:
  enable: true
  title: "Bindings"
  sections:
    - link: https://pypi.org/project/prql-python
      label: "prql-python"
      text: Python bindings for prql-compiler.

    - link: https://www.npmjs.com/package/prql-js
      label: "prql-js"
      text: "JavaScript bindings for prql-compiler."

    - link: https://crates.io/crates/prql-compiler
      label: "prql-compiler"
      text: |
        PRQL's compiler library, written in Rust.

        `cargo install prql-compiler`

comments_section:
  enable: true
  title: "What people are saying"
  comments:
    # NB: The tweets use a custom shortcode, since we want to limit the media & conversation.
    - quote:
        text: It starts with FROM, it fixes trailing commas, and it's called PRQL?? If this is a dream, don't wake me up.
        author: Jeremiah Lowin, Founder & CEO, Prefect.
    - tweet: "{{< tweet 1522562664467107840 >}}"
    - tweet: "{{< tweet 1485965394880131081 >}}"
    - quote:
        text: Column aliases would have saved me hundreds of hours over the course of my career.
        author: "@dvasdekis"
        link: https://news.ycombinator.com/item?id=30064873
    - tweet: "{{< tweet 1514280454890872833 >}}"
    - tweet: "{{< tweet 1485958835844100098 >}}"
    - quote:
        text:
          Having written some complex dbt projects...the first thing...it gets
          right is to start with the table and work down. This is
          an enormous readability boost in large projects and leads to great intellisense.
        author: Ruben Slabbert
        link: https://lobste.rs/s/oavgcx/prql_simpler_more_powerful_sql#c_nmzcd7
    - tweet: "{{< tweet 1485795181198983170 >}}"
    - quote:
        text: Just wanna say, I absolutely love this.
        author: Alex Kritchevsky
        link: https://news.ycombinator.com/item?id=30063771
---
