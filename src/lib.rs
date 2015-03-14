// Copyright 2012-2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#![feature(rustc_private)]

extern crate syntax;

use syntax::ast;
use syntax::codemap::Spanned;
use syntax::ext::base::ExtCtxt;
use syntax::owned_slice::OwnedSlice;
use syntax::parse::token;
use syntax::parse;
use syntax::print::pprust;
use syntax::ptr::P;

use syntax::ast::{TokenTree, Generics, Expr};

pub use syntax::parse::new_parser_from_tts;
pub use syntax::codemap::{BytePos, Span, dummy_spanned};

pub trait ToTokens {
    fn to_tokens(&self, cx: &ExtCtxt) -> Vec<TokenTree>;
}

impl ToTokens for TokenTree {
    fn to_tokens(&self, _cx: &ExtCtxt) -> Vec<TokenTree> {
        vec!(self.clone())
    }
}

impl<T: ToTokens> ToTokens for Vec<T> {
    fn to_tokens(&self, cx: &ExtCtxt) -> Vec<TokenTree> {
        self.iter()
            .flat_map(|t| t.to_tokens(cx).into_iter())
            .collect()
    }
}

impl<T: ToTokens> ToTokens for Spanned<T> {
    fn to_tokens(&self, cx: &ExtCtxt) -> Vec<TokenTree> {
        // FIXME: use the span?
        self.node.to_tokens(cx)
    }
}

impl<T: ToTokens> ToTokens for Option<T> {
    fn to_tokens(&self, cx: &ExtCtxt) -> Vec<TokenTree> {
        match self {
            &Some(ref t) => t.to_tokens(cx),
            &None => Vec::new(),
        }
    }
}

/* Should be (when bugs in default methods are fixed):

trait ToSource : ToTokens {
    // Takes a thing and generates a string containing rust code for it.
    pub fn to_source() -> String;

    // If you can make source, you can definitely make tokens.
    pub fn to_tokens(cx: &ExtCtxt) -> ~[TokenTree] {
        cx.parse_tts(self.to_source())
    }
}

*/

// FIXME: Move this trait to pprust and get rid of *_to_str?
pub trait ToSource {
    // Takes a thing and generates a string containing rust code for it.
    fn to_source(&self) -> String;
}

// FIXME (Issue #16472): This should go away after ToToken impls
// are revised to go directly to token-trees.
trait ToSourceWithHygiene : ToSource {
    // Takes a thing and generates a string containing rust code
    // for it, encoding Idents as special byte sequences to
    // maintain hygiene across serialization and deserialization.
    fn to_source_with_hygiene(&self) -> String;
}

macro_rules! impl_to_source {
    (P<$t:ty>, $pp:ident) => (
        impl ToSource for P<$t> {
            fn to_source(&self) -> String {
                pprust::$pp(&**self)
            }
        }
        impl ToSourceWithHygiene for P<$t> {
            fn to_source_with_hygiene(&self) -> String {
                pprust::with_hygiene::$pp(&**self)
            }
        }
    );
    ($t:ty, $pp:ident) => (
        impl ToSource for $t {
            fn to_source(&self) -> String {
                pprust::$pp(self)
            }
        }
        impl ToSourceWithHygiene for $t {
            fn to_source_with_hygiene(&self) -> String {
                pprust::with_hygiene::$pp(self)
            }
        }
    );
}

fn slice_to_source<'a, T: ToSource>(sep: &'static str, xs: &'a [T]) -> String {
    xs.iter()
        .map(|i| i.to_source())
        .collect::<Vec<String>>()
        .connect(sep)
        .to_string()
}

fn slice_to_source_with_hygiene<'a, T: ToSourceWithHygiene>(
    sep: &'static str, xs: &'a [T]) -> String {
    xs.iter()
        .map(|i| i.to_source_with_hygiene())
        .collect::<Vec<String>>()
        .connect(sep)
        .to_string()
}

macro_rules! impl_to_source_slice {
    ($t:ty, $sep:expr) => (
        impl ToSource for [$t] {
            fn to_source(&self) -> String {
                slice_to_source($sep, self)
            }
        }

        impl ToSourceWithHygiene for [$t] {
            fn to_source_with_hygiene(&self) -> String {
                slice_to_source_with_hygiene($sep, self)
            }
        }
    )
}

impl ToSource for ast::Ident {
    fn to_source(&self) -> String {
        token::get_ident(*self).to_string()
    }
}

impl ToSourceWithHygiene for ast::Ident {
    fn to_source_with_hygiene(&self) -> String {
        self.encode_with_hygiene()
    }
}

impl_to_source! { ast::Path, path_to_string }
impl_to_source! { ast::Ty, ty_to_string }
impl_to_source! { ast::Block, block_to_string }
impl_to_source! { ast::Arg, arg_to_string }
impl_to_source! { Generics, generics_to_string }
impl_to_source! { P<ast::Item>, item_to_string }
impl_to_source! { P<ast::Stmt>, stmt_to_string }
impl_to_source! { P<ast::Expr>, expr_to_string }
impl_to_source! { P<ast::Pat>, pat_to_string }
impl_to_source! { ast::Arm, arm_to_string }
impl_to_source_slice! { ast::Ty, ", " }
impl_to_source_slice! { P<ast::Item>, "\n\n" }

impl ToSource for ast::Attribute_ {
    fn to_source(&self) -> String {
        pprust::attribute_to_string(&dummy_spanned(self.clone()))
    }
}
impl ToSourceWithHygiene for ast::Attribute_ {
    fn to_source_with_hygiene(&self) -> String {
        self.to_source()
    }
}

impl ToSource for P<ast::ImplItem> {
    fn to_source(&self) -> String {
        pprust::to_string(|s| s.print_impl_item(self))
    }
}

impl ToSourceWithHygiene for P<ast::ImplItem> {
    fn to_source_with_hygiene(&self) -> String {
        pprust::with_hygiene::to_string_hyg(|s| s.print_impl_item(self))
    }
}

impl ToSource for ast::WhereClause {
    fn to_source(&self) -> String {
        pprust::to_string(|s| {
            s.print_where_clause(&ast::Generics {
                lifetimes: vec![],
                ty_params: OwnedSlice::empty(),
                where_clause: self.clone(),
            })
        })
    }
}

impl ToSourceWithHygiene for ast::WhereClause {
    fn to_source_with_hygiene(&self) -> String {
        pprust::with_hygiene::to_string_hyg(|s| {
            s.print_where_clause(&ast::Generics {
                lifetimes: vec![],
                ty_params: OwnedSlice::empty(),
                where_clause: self.clone(),
            })
        })
    }
}

impl ToSource for str {
    fn to_source(&self) -> String {
        let lit = dummy_spanned(ast::LitStr(
                token::intern_and_get_ident(self), ast::CookedStr));
        pprust::lit_to_string(&lit)
    }
}
impl ToSourceWithHygiene for str {
    fn to_source_with_hygiene(&self) -> String {
        self.to_source()
    }
}

impl ToSource for () {
    fn to_source(&self) -> String {
        "()".to_string()
    }
}
impl ToSourceWithHygiene for () {
    fn to_source_with_hygiene(&self) -> String {
        self.to_source()
    }
}

impl ToSource for bool {
    fn to_source(&self) -> String {
        let lit = dummy_spanned(ast::LitBool(*self));
        pprust::lit_to_string(&lit)
    }
}
impl ToSourceWithHygiene for bool {
    fn to_source_with_hygiene(&self) -> String {
        self.to_source()
    }
}

impl ToSource for char {
    fn to_source(&self) -> String {
        let lit = dummy_spanned(ast::LitChar(*self));
        pprust::lit_to_string(&lit)
    }
}
impl ToSourceWithHygiene for char {
    fn to_source_with_hygiene(&self) -> String {
        self.to_source()
    }
}

macro_rules! impl_to_source_isize {
    (signed, $t:ty, $tag:expr) => (
        impl ToSource for $t {
            fn to_source(&self) -> String {
                let lit = ast::LitInt(*self as u64, ast::SignedIntLit($tag,
                                                                      ast::Sign::new(*self)));
                pprust::lit_to_string(&dummy_spanned(lit))
            }
        }
        impl ToSourceWithHygiene for $t {
            fn to_source_with_hygiene(&self) -> String {
                self.to_source()
            }
        }
    );
    (unsigned, $t:ty, $tag:expr) => (
        impl ToSource for $t {
            fn to_source(&self) -> String {
                let lit = ast::LitInt(*self as u64, ast::UnsignedIntLit($tag));
                pprust::lit_to_string(&dummy_spanned(lit))
            }
        }
        impl ToSourceWithHygiene for $t {
            fn to_source_with_hygiene(&self) -> String {
                self.to_source()
            }
        }
    );
}

impl_to_source_isize! { signed, isize, ast::TyIs(false) }
impl_to_source_isize! { signed, i8,  ast::TyI8 }
impl_to_source_isize! { signed, i16, ast::TyI16 }
impl_to_source_isize! { signed, i32, ast::TyI32 }
impl_to_source_isize! { signed, i64, ast::TyI64 }

impl_to_source_isize! { unsigned, usize, ast::TyUs(false) }
impl_to_source_isize! { unsigned, u8,   ast::TyU8 }
impl_to_source_isize! { unsigned, u16,  ast::TyU16 }
impl_to_source_isize! { unsigned, u32,  ast::TyU32 }
impl_to_source_isize! { unsigned, u64,  ast::TyU64 }

// Alas ... we write these out instead. All redundant.

macro_rules! impl_to_tokens {
    ($t:ty) => (
        impl ToTokens for $t {
            fn to_tokens(&self, cx: &ExtCtxt) -> Vec<TokenTree> {
                cx.parse_tts_with_hygiene(self.to_source_with_hygiene())
            }
        }
    )
}

macro_rules! impl_to_tokens_lifetime {
    ($t:ty) => (
        impl<'a> ToTokens for $t {
            fn to_tokens(&self, cx: &ExtCtxt) -> Vec<TokenTree> {
                cx.parse_tts_with_hygiene(self.to_source_with_hygiene())
            }
        }
    )
}

impl_to_tokens! { ast::Ident }
impl_to_tokens! { ast::Path }
impl_to_tokens! { P<ast::Item> }
impl_to_tokens! { P<ast::ImplItem> }
impl_to_tokens! { ast::WhereClause }
impl_to_tokens! { P<ast::Pat> }
impl_to_tokens! { ast::Arm }
impl_to_tokens_lifetime! { &'a [P<ast::Item>] }
impl_to_tokens! { ast::Ty }
impl_to_tokens_lifetime! { &'a [ast::Ty] }
impl_to_tokens! { Generics }
impl_to_tokens! { P<ast::Stmt> }
impl_to_tokens! { P<ast::Expr> }
impl_to_tokens! { ast::Block }
impl_to_tokens! { ast::Arg }
impl_to_tokens! { ast::Attribute_ }
impl_to_tokens_lifetime! { &'a str }
impl_to_tokens! { () }
impl_to_tokens! { char }
impl_to_tokens! { bool }
impl_to_tokens! { isize }
impl_to_tokens! { i8 }
impl_to_tokens! { i16 }
impl_to_tokens! { i32 }
impl_to_tokens! { i64 }
impl_to_tokens! { usize }
impl_to_tokens! { u8 }
impl_to_tokens! { u16 }
impl_to_tokens! { u32 }
impl_to_tokens! { u64 }

pub trait ExtParseUtils {
    fn parse_item(&self, s: String) -> P<ast::Item>;
    fn parse_expr(&self, s: String) -> P<ast::Expr>;
    fn parse_stmt(&self, s: String) -> P<ast::Stmt>;
    fn parse_tts(&self, s: String) -> Vec<ast::TokenTree>;
}

trait ExtParseUtilsWithHygiene {
    // FIXME (Issue #16472): This should go away after ToToken impls
    // are revised to go directly to token-trees.
    fn parse_tts_with_hygiene(&self, s: String) -> Vec<ast::TokenTree>;
}

impl<'a> ExtParseUtils for ExtCtxt<'a> {

    fn parse_item(&self, s: String) -> P<ast::Item> {
        parse::parse_item_from_source_str(
            "<quote expansion>".to_string(),
            s,
            self.cfg(),
            self.parse_sess()).expect("parse error")
    }

    fn parse_stmt(&self, s: String) -> P<ast::Stmt> {
        parse::parse_stmt_from_source_str("<quote expansion>".to_string(),
                                          s,
                                          self.cfg(),
                                          Vec::new(),
                                          self.parse_sess())
    }

    fn parse_expr(&self, s: String) -> P<ast::Expr> {
        parse::parse_expr_from_source_str("<quote expansion>".to_string(),
                                          s,
                                          self.cfg(),
                                          self.parse_sess())
    }

    fn parse_tts(&self, s: String) -> Vec<ast::TokenTree> {
        parse::parse_tts_from_source_str("<quote expansion>".to_string(),
                                         s,
                                         self.cfg(),
                                         self.parse_sess())
    }
}

impl<'a> ExtParseUtilsWithHygiene for ExtCtxt<'a> {

    fn parse_tts_with_hygiene(&self, s: String) -> Vec<ast::TokenTree> {
        use syntax::parse::with_hygiene::parse_tts_from_source_str;
        parse_tts_from_source_str("<quote expansion>".to_string(),
                                  s,
                                  self.cfg(),
                                  self.parse_sess())
    }
}
