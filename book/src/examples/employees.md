# Employees

These are homework tasks on [employees database](https://github.com/vrajmohan/pgsql-sample-data.git).

Clone and init the database (requires a local PostgreSQL instance):

    $ psql -U postgres -c 'CREATE DATABASE employees;'
    $ git clone https://github.com/vrajmohan/pgsql-sample-data.git
    $ psql -U postgres -d employees -f pgsql-sample-data/employee/employees.dump

Execute a PRQL query:

    $ cd prql-compiler
    $ cargo run compile examples/employees/average-title-salary.prql | psql -U postgres -d employees

## Task 1

> rank the employee titles according to the average salary for each department.

My solution:

- for each employee, find their average salary,
- join employees with their departments and titles (duplicating employees for each of their titles and departments)
- group by department and title, aggregating average salary
- join with department to get department name

```prql
from salaries
group [emp_no] (
  aggregate [emp_salary = average salary]
)
join t=titles [emp_no]
join dept_emp side:left [emp_no]
group [dept_emp.dept_no, t.title] (
  aggregate [avg_salary = average emp_salary]
)
join departments [dept_no]
select [dept_name, title, avg_salary]
```

## Task 2

> Estimate distribution of salaries and gender for each department departments.

```prql
from employees
join salaries [emp_no]
group [emp_no, gender] (
  aggregate [
    emp_salary = average salary
  ]
)
join de=dept_emp [emp_no] side:left
group [de.dept_no, gender] (
  aggregate [
    salary_avg = average emp_salary,
    salary_sd = stddev emp_salary,
  ]
)
join departments [dept_no]
select [dept_name, gender, salary_avg, salary_sd]
```

## Task 3

> Estimate distribution of salaries and gender for each manager.

```prql
from employees
join salaries [emp_no]
group [emp_no, gender] (
  aggregate [
    emp_salary = average salary
  ]
)
join de=dept_emp [emp_no]
join dm=dept_manager [
  (dm.dept_no == de.dept_no) and s"(de.from_date, de.to_date) OVERLAPS (dm.from_date, dm.to_date)"
]
group [dm.emp_no, gender] (
  aggregate [
    salary_avg = average emp_salary,
    salary_sd = stddev emp_salary
  ]
)
derive mng_no = dm.emp_no
join managers=employees [emp_no]
derive mng_name = s"managers.first_name || ' ' || managers.last_name"
select [mng_name, managers.gender, salary_avg, salary_sd]
```

## Task 4

> Find distributions of titles, salaries and genders for each department.

```prql
from de=dept_emp
join s=salaries side:left [
  (s.emp_no == de.emp_no),
  s"({s.from_date}, {s.to_date}) OVERLAPS ({de.from_date}, {de.to_date})"
]
group [de.emp_no, de.dept_no] (
  aggregate salary = (average s.salary)
)
join employees [emp_no]
join titles [emp_no]
select [dept_no, salary, employees.gender, titles.title]
```
