// Syntax highlighting for PRQL.

// Keep consistent with
// https://github.com/prql/prql/blob/main/website/themes/prql-theme/static/highlight/prql.js
// TODO: can we import one from the other at build time?

// Inspired by [Pest's book](https://github.com/pest-parser/book)

// mdBook exposes a minified version of highlight.js, so the language
// definition objects below have abbreviated property names:
//     "b"  => begin
//     "e"  => end
//     "c"  => contains
//     "k"  => keywords
//     "cN" => className

formatting = function (hljs) {
  const TRANSFORMS = [
    "from",
    "select",
    "derive",
    "filter",
    "take",
    "sort",
    "join",
    "aggregate",
    "func",
    "group",
    "window",
    "prql",
  ];
  return {
    name: "PRQL",
    case_insensitive: true,
    keywords: {
      keyword: TRANSFORMS,
      literal: "false true null and or not",
    },
    contains: [
      hljs.COMMENT("#", "$"),
      {
        // named arg
        scope: "params",
        begin: /\w+\s*:/,
        end: "",
        relevance: 10,
      },
      {
        // assign
        scope: { 1: "variable" },
        match: [/\w+\s*/, /=[^=]/],
        relevance: 10,
      },
      {
        // date
        scope: "string",
        match: /@(\d*|-|\.\d|:)+/,
        relevance: 10,
      },
      {
        // interpolation string
        scope: "attribute",
        begin: '(s|f)"',
        end: '"',
        relevance: 10,
      },

      {
        // normal string
        scope: "string",
        begin: '"',
        end: '"',
        relevance: 10,
      },
      {
        // number
        scope: "number",
        // Slightly modified from https://stackoverflow.com/a/23872060/3064736;
        // it requires a number after a decimal point, so ranges appear as ranges.
        match: /[+-]?((\d+(\.\d+)?)|(\.\d+))/,
        relevance: 10,
      },
      {
        // range
        scope: "symbol",
        match: /\.{2}/,
        relevance: 10,
      },

      // Unfortunately this just overrides any keywords. It's also not
      // complete — it only handles functions at the beginning of a line.
      // I spent several hours trying to get hljs to handle this, but
      // because there's no recursion, I'm not sure it's possible.
      // Possibly we could hook into `on:begin` and implement it
      // ourselves, but this would be a lot of overhead.
      // { // function
      //     keywords: TRANSFORMS.join(' '),
      //     beginScope: { 1: 'title.function' },
      //     begin: [/^\s*[a-zA-Z]+/, /(\s+[a-zA-Z]+)+/],
      //     relevance: 10
      // },

      // I couldn't seem to get this working, and other languages don't seem
      // to use it.
      // { // operator
      //     match: [/-/, /\*/], //,'/', '%', '+', '-', '==', '!=', '>', '<', '>=', '<=', '??']
      // {
    ],
  };
};

hljs.registerLanguage("prql", formatting);
hljs.registerLanguage("prql_no_test", formatting);
hljs.registerLanguage("elm", formatting);

// These lines should only exists in the book, not the website.

// This file is inserted after the default highlight.js invocation, which tags
// unknown-language blocks with CSS classes but doesn't highlight them.
Array.from(document.querySelectorAll("code.language-prql")).forEach(
  (a) => console.log(a) || hljs.highlightBlock(a)
);

Array.from(document.querySelectorAll("code.language-prql_no_test")).forEach(
  (a) => console.log(a) || hljs.highlightBlock(a)
);

Array.from(document.querySelectorAll("code.language-elm")).forEach(
  (a) => console.log(a) || hljs.highlightBlock(a)
);
