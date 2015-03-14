// Copyright 2012-2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#![feature(plugin, rustc_private)]
#![plugin(quasi_macros)]

extern crate syntax;
extern crate quasi;

use syntax::ext::base::ExtCtxt;
use syntax::ext::expand;
use syntax::parse;
use syntax::print::pprust;

fn make_ext_ctxt(sess: &parse::ParseSess) -> ExtCtxt {
    let info = syntax::codemap::ExpnInfo {
        call_site: syntax::codemap::DUMMY_SP,
        callee: syntax::codemap::NameAndSpan {
            name: "test".to_string(),
            format: syntax::codemap::MacroAttribute,
            allow_internal_unstable: false,
            span: None
        }
    };

    let cfg = vec![];
    let ecfg = expand::ExpansionConfig {
        crate_name: String::new(),
        features: None,
        recursion_limit: 64,
    };

    let mut cx = ExtCtxt::new(&sess, cfg, ecfg);
    cx.bt_push(info);

    cx
}

#[test]
fn test_quote_tokens() {
    let sess = parse::new_parse_sess();
    let cx = make_ext_ctxt(&sess);

    let tts = quote_tokens!(&cx, (+ 2 3));
    assert_eq!(pprust::tts_to_string(&tts), "( + 2 3 )");
}

#[test]
fn test_quote_ty() {
    let sess = parse::new_parse_sess();
    let cx = make_ext_ctxt(&sess);

    let ty = quote_ty!(&cx, isize);
    assert_eq!(pprust::ty_to_string(&ty), "isize");
}

#[test]
fn test_quote_expr() {
    let sess = parse::new_parse_sess();
    let cx = make_ext_ctxt(&sess);

    let expr = quote_expr!(&cx, 23);
    assert_eq!(pprust::expr_to_string(&expr), "23");

    let value = 24;
    let expr = quote_expr!(&cx, $value);
    assert_eq!(pprust::expr_to_string(&expr), "24i32");
}

#[test]
fn test_quote_stmt() {
    let sess = parse::new_parse_sess();
    let cx = make_ext_ctxt(&sess);

    let stmt = quote_stmt!(&cx, let x = 20;);
    assert_eq!(pprust::stmt_to_string(&stmt), "let x = 20;");
}

#[test]
fn test_quote_pat() {
    let sess = parse::new_parse_sess();
    let cx = make_ext_ctxt(&sess);

    let pat = quote_pat!(&cx, Some(_));
    assert_eq!(pprust::pat_to_string(&pat), "Some(_)");
}

#[test]
fn test_quote_arm() {
    let sess = parse::new_parse_sess();
    let cx = make_ext_ctxt(&sess);

    let arm = quote_arm!(&cx, (ref x, ref y) => (x, y),);
    assert_eq!(pprust::arm_to_string(&arm), " (ref x, ref y) => (x, y),");
}

#[test]
fn test_quote_block() {
    let sess = parse::new_parse_sess();
    let cx = make_ext_ctxt(&sess);

    let block = quote_block!(&cx, {
        let x = 5;
        let y = 6;
        x + y
    });

    assert_eq!(
        pprust::block_to_string(&block),
        "{ let x = 5; let y = 6; x + y }");
}

#[test]
fn test_quote_item() {
    let sess = parse::new_parse_sess();
    let cx = make_ext_ctxt(&sess);

    let item = quote_item!(&cx, static x : int = 10;).unwrap();
    assert_eq!(pprust::item_to_string(&item), "static x: int = 10;");
}

#[test]
fn test_quote_impl_item() {
    let sess = parse::new_parse_sess();
    let cx = make_ext_ctxt(&sess);

    let impl_item = quote_impl_item!(&cx, fn method(&mut self, x: u32) -> u32 { x });
    assert_eq!(
        pprust::to_string(|s| s.print_impl_item(&impl_item)),
        "fn method(&mut self, x: u32) -> u32 { x }"
    );
}

#[test]
fn test_quote_where_clause() {
    let sess = parse::new_parse_sess();
    let cx = make_ext_ctxt(&sess);

    let where_clause = quote_where_clause!(&cx, where A, B: T);
    assert_eq!(
        pprust::to_string(|s| s.print_where_clause(&where_clause)),
        "where A, B: T"
    );
}

#[test]
fn test_quote_with_macro() {
    let sess = parse::new_parse_sess();
    let cx = make_ext_ctxt(&sess);

    let block = quote_block!(&cx, {
        macro_rules! value { () => 6 }
        value!()
    });

    assert_eq!(
        pprust::block_to_string(&block),
        "{\n    macro_rules! value((  ) => 6);\n    value!()\n}");

    // Make sure we don't expand macros in the quote.
    macro_rules! value { () => 5 }
    let block = quote_block!(&cx, { value!() });

    assert_eq!(pprust::block_to_string(&block), "{ value!() }");
}
