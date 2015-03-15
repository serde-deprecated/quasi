Rust quasi-quoting macro.

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
    let expr = quote_expr!(cx, 1 + 2);

    // prints `1 + 2`.
    println!("{}", syntax::pprint::expr_to_string(&expr));
}
```
