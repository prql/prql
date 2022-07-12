# prql-js

JavaScript bindings for [`prql-compiler`](https://github.com/prql/prql/). Check out <https://prql-lang.org> for more
context.

## Installation

```sh
npm install prql-js
```

## Usage

Currently these functions are exposed

```javascript
function compile(prql_string) # returns CompileResult
function to_sql(prql_string) # returns SQL string
function to_json(prql_string) # returns JSON string ( needs JSON.parse() to get the json)
```

### From NodeJS

```javascript
const prql = require("prql-js");

const { sql, error } = compile(`from employees | select first_name`);
console.log(sql);
// handle error as well...
```

### From a Browser

```html
<html>
  <head>
    <script src="./node_modules/prql-js/dist/web/prql_js.js"></script>
    <script>
      const { compile } = wasm_bindgen;

      async function run() {
        await wasm_bindgen("./node_modules/prql-js/dist/web/prql_js_bg.wasm");
        const { sql, error } = compile("from employees | select first_name");

        console.log(sql);
        // handle error as well...
      }

      run();
    </script>
  </head>

  <body></body>
</html>
```

### From a Framework or a Bundler

```typescript
import compile from "prql-js/dist/bundler";

const { sql, error } = compile(`from employees | select first_name`);
console.log(sql);
// handle error as well...
```

## Notes

This uses
[`wasm-pack`](https://rustwasm.github.io/docs/wasm-pack/tutorials/npm-browser-packages/index.html)
to generate bindings[^1].

[^1]:

though we would be very open to other approaches, and used `trunk`
successfully in a rust-driven approach to this, RIP `prql-web`.

## Development

Build:

```sh
npm run build-all
```

This builds Node, bundler and web packages in the `dist` path.

Test:

```sh
wasm-pack test --firefox
```
