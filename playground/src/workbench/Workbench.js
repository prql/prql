import "./Workbench.css";

import React from "react";
import * as prql from "prql-js/dist/bundler";

import * as monacoTheme from "./monaco-theme.json";
import * as monaco from "monaco-editor";
import Editor, { loader } from "@monaco-editor/react";
import prqlSyntax from "./prql-syntax";

import { Light as SyntaxHighlighter } from "react-syntax-highlighter";
import sql from "react-syntax-highlighter/dist/esm/languages/hljs/sql";

SyntaxHighlighter.registerLanguage("sql", sql);

loader.config({ monaco });

class Workbench extends React.Component {
  monaco = null;
  editor = null;

  state = {
    filename: "input.prql",
    sql: "",
    prql: "",
  };

  loadFile(filename, content) {
    this.setState({ filename, prql: content });
    if (this.editor) {
      this.editor.setValue(content);
    }
  }

  componentDidMount() {
    this.props.setCallables({ loadFile: (f, c) => this.loadFile(f, c) });
  }

  beforeEditorMount(monaco) {
    this.monaco = monaco;
    monaco.editor.defineTheme("blackboard", monacoTheme);
    monaco.languages.register({ id: "prql", extensions: ["prql"] });
    monaco.languages.setMonarchTokensProvider("prql", prqlSyntax);
  }

  onEditorMount(editor) {
    this.editor = editor;

    this.compile(editor.getValue());
  }

  compile(value) {
    this.setState({ prql: value });

    const result = prql.compile(value);

    if (result.sql) {
      this.setState({ sql: result.sql, errorMessage: null });
    }

    if (result.error) {
      this.setState({ errorMessage: result.error.message });

      const errors = [
        {
          severity: "error",
          message: result.error.message,
          startLineNumber: result.error.location?.start_line + 1,
          startColumn: result.error.location?.start_column + 1,
          endLineNumber: result.error.location?.end_line + 1,
          endColumn: result.error.location?.end_column + 1,
        },
      ];
      this.monaco.editor.setModelMarkers(
        this.editor.getModel(),
        "prql",
        errors
      );
    } else {
      this.monaco.editor.setModelMarkers(this.editor.getModel(), "prql", []);
    }
  }

  save() {
    if (!this.editor) return;

    this.props.onSaveFile(this.state.filename, this.state.prql);
  }

  rename() {
    let filename = prompt(`New name for ${this.state.filename}`);
    if (filename) {
      if (!filename.endsWith(".prql")) {
        filename += ".prql";
      }
      this.setState({ filename });
    }
  }

  render() {
    return (
      <div className="column">
        <div className="tabs">
          <div className="tab">
            <div className="tab-top">
              <div className="tab-title">{this.state.filename}</div>

              <div className="spacer"></div>

              <button onClick={() => this.rename()}>Rename</button>
              <button onClick={() => this.save()}>Save</button>
            </div>
            <Editor
              height="10rem"
              defaultLanguage="prql"
              defaultValue={this.state.prql}
              onChange={(v) => this.compile(v)}
              onMount={(e, m) => this.onEditorMount(e, m)}
              beforeMount={(m) => this.beforeEditorMount(m)}
              theme="blackboard"
              options={{
                minimap: { enabled: false },
                scrollBeyondLastLine: false,
              }}
            />
          </div>

          <div className="tab">
            <div className="tab-title">output.sql</div>

            <SyntaxHighlighter language="sql" useInlineStyles={false}>
              {this.state.sql}
            </SyntaxHighlighter>
          </div>
        </div>

        {this.state.errorMessage && (
          <div className="error-pane">{this.state.errorMessage}</div>
        )}
      </div>
    );
  }
}

export default Workbench;
