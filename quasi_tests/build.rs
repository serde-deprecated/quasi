extern crate quasi_codegen;

use std::env;
use std::path::Path;

pub fn main() {
    let out_dir = env::var_os("OUT_DIR").unwrap();

    let src = Path::new("tests/test.rs.in");
    let dst = Path::new(&out_dir).join("test.rs");

    quasi_codegen::expand(&src, &dst).unwrap();
}
