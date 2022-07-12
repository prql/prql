# Ranges

PRQL has a concise range syntax `start..end`.

This can be used in filters with the `in` function, with any type of literal,
including dates:

```prql
from events
filter (date | in @1776-07-04..@1787-09-17)
filter (magnitude | in 50..100)
```

Like in SQL, ranges are inclusive.

As discussed in the [take](../transforms/take.md) docs, ranges can also be used
in `take`:

```prql
from orders
sort [-value, date]
take 101..110
```

## Roadmap

We'd like to use this for more like whether an object is in an array or list literal.
