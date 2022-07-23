# Rust (prql-compiler)

## Installation

```
cargo new myproject
cd myproject
cargo install prql-compiler
```

## Usage

`cargo run`
####src/main.rs:

```rust
use prql_compiler::compile;

fn main() {
    let prql = "from employees | select [name,age]  ";
    let sql = compile(prql).unwrap();
    println!("{:?}", sql.replace("\n", " "));
}

```

####Cargo.toml:

```
[package]
name = "myproject"
version = "0.1.0"
edition = "2021"

[dependencies]
prql-compiler = "0.2.2"
```
