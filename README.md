Rust Quasi-Quoting Syntax Extension
===================================

[![Build Status](https://api.travis-ci.org/serde-rs/quasi.svg?branch=master)](https://travis-ci.org/serde-rs/quasi)
[![Latest Version](https://img.shields.io/crates/v/quasi.svg)](https://crates.io/crates/quasi)

Quasi is a quasi-quotation macro library that allows you produce Rust AST from
Rust syntax. Furthermore, it allows you to easily splice local variables into
the quoted string in order to have it inserted into the produced AST.

Example
-------

Here is a simple example to build the `syntax::ast::Expr` that
represents adding two numbers together:

```rust
#![feature(plugin, rustc_private)]
#![plugin(quasi_macros)]

extern crate syntax;
extern crate quasi;

use syntax::ext::base::ExtCtxt;

fn make_ext_ctxt(...) -> ExtCtxt {
    ...
}

fn main() {
    let cx = make_ext_ctxt(...);
    let y = 2;
    let expr = quote_expr!(cx, 1 + $y);

    // prints `1 + 2`.
    println!("{}", syntax::pprint::expr_to_string(&expr));
}
```
