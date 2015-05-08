// Copyright 2012 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#![feature(plugin_registrar, unboxed_closures, rustc_private)]

extern crate quasi_codegen;
extern crate rustc;

use rustc::plugin::Registry;

#[plugin_registrar]
#[doc(hidden)]
pub fn plugin_registrar(reg: &mut Registry) {
    reg.register_macro("quote_tokens", quasi_codegen::expand_quote_tokens);
    reg.register_macro("quote_ty", quasi_codegen::expand_quote_ty);
    reg.register_macro("quote_expr", quasi_codegen::expand_quote_expr);
    reg.register_macro("quote_matcher", quasi_codegen::expand_quote_matcher);
    reg.register_macro("quote_stmt", quasi_codegen::expand_quote_stmt);
    reg.register_macro("quote_attr", quasi_codegen::expand_quote_attr);
    reg.register_macro("quote_pat", quasi_codegen::expand_quote_pat);
    reg.register_macro("quote_arm", quasi_codegen::expand_quote_arm);
    reg.register_macro("quote_block", quasi_codegen::expand_quote_block);
    reg.register_macro("quote_item", quasi_codegen::expand_quote_item);
    reg.register_macro("quote_impl_item", quasi_codegen::expand_quote_impl_item);
    //reg.register_macro("quote_where_clause", quasi_codegen::expand_quote_where_clause);
}
