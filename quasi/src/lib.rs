// Copyright 2012-2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#![feature(collections, rustc_private)]

extern crate syntax;

use std::rc::Rc;

use syntax::ast::{self, TokenTree, Generics, Expr};
use syntax::codemap::{DUMMY_SP, Spanned, dummy_spanned};
use syntax::ext::base::ExtCtxt;
use syntax::parse::{self, classify, parse_tts_from_source_str, token};
use syntax::print::pprust;
use syntax::ptr::P;

pub trait ToTokens {
    fn to_tokens(&self, _cx: &ExtCtxt) -> Vec<TokenTree>;
}

impl ToTokens for TokenTree {
    fn to_tokens(&self, _cx: &ExtCtxt) -> Vec<TokenTree> {
        vec!(self.clone())
    }
}

impl<'a, T: ToTokens> ToTokens for &'a T {
    fn to_tokens(&self, cx: &ExtCtxt) -> Vec<TokenTree> {
        (**self).to_tokens(cx)
    }
}

impl<'a, T: ToTokens> ToTokens for &'a [T] {
    fn to_tokens(&self, cx: &ExtCtxt) -> Vec<TokenTree> {
        self.iter()
            .flat_map(|t| t.to_tokens(cx).into_iter())
            .collect()
    }
}

impl<T: ToTokens> ToTokens for Vec<T> {
    fn to_tokens(&self, cx: &ExtCtxt) -> Vec<TokenTree> {
        self.iter().flat_map(|t| t.to_tokens(cx).into_iter()).collect()
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

impl ToTokens for ast::Ident {
    fn to_tokens(&self, _cx: &ExtCtxt) -> Vec<TokenTree> {
        vec![ast::TtToken(DUMMY_SP, token::Ident(*self, token::Plain))]
    }
}

impl ToTokens for ast::Path {
    fn to_tokens(&self, _cx: &ExtCtxt) -> Vec<TokenTree> {
        vec![ast::TtToken(DUMMY_SP, token::Interpolated(token::NtPath(Box::new(self.clone()))))]
    }
}

impl ToTokens for ast::Ty {
    fn to_tokens(&self, _cx: &ExtCtxt) -> Vec<TokenTree> {
        vec![ast::TtToken(self.span, token::Interpolated(token::NtTy(P(self.clone()))))]
    }
}

impl ToTokens for P<ast::Ty> {
    fn to_tokens(&self, _cx: &ExtCtxt) -> Vec<TokenTree> {
        vec![ast::TtToken(self.span, token::Interpolated(token::NtTy(self.clone())))]
    }
}

impl ToTokens for P<ast::Block> {
    fn to_tokens(&self, _cx: &ExtCtxt) -> Vec<TokenTree> {
        vec![ast::TtToken(self.span, token::Interpolated(token::NtBlock(self.clone())))]
    }
}

impl ToTokens for P<ast::Item> {
    fn to_tokens(&self, _cx: &ExtCtxt) -> Vec<TokenTree> {
        vec![ast::TtToken(self.span, token::Interpolated(token::NtItem(self.clone())))]
    }
}

impl ToTokens for P<ast::ImplItem> {
    fn to_tokens(&self, _cx: &ExtCtxt) -> Vec<TokenTree> {
        vec![ast::TtToken(self.span, token::Interpolated(token::NtImplItem(self.clone())))]
    }
}

impl ToTokens for P<ast::TraitItem> {
    fn to_tokens(&self, _cx: &ExtCtxt) -> Vec<TokenTree> {
        vec![ast::TtToken(self.span, token::Interpolated(token::NtTraitItem(self.clone())))]
    }
}

impl ToTokens for ast::Generics {
    fn to_tokens(&self, cx: &ExtCtxt) -> Vec<TokenTree> {
        let s = pprust::generics_to_string(self);

        parse_tts_from_source_str("<quote expansion".to_string(), s, cx.cfg(), cx.parse_sess())
    }
}

impl ToTokens for ast::WhereClause {
    fn to_tokens(&self, cx: &ExtCtxt) -> Vec<TokenTree> {
        let s = pprust::to_string(|s| {
            s.print_where_clause(&self)
        });

        parse_tts_from_source_str("<quote expansion".to_string(), s, cx.cfg(), cx.parse_sess())
    }
}

impl ToTokens for P<ast::Stmt> {
    fn to_tokens(&self, _cx: &ExtCtxt) -> Vec<TokenTree> {
        let mut tts = vec![
            ast::TtToken(self.span, token::Interpolated(token::NtStmt(self.clone())))
        ];

        // Some statements require a trailing semicolon.
        if classify::stmt_ends_with_semi(&self.node) {
            tts.push(ast::TtToken(self.span, token::Semi));
        }

        tts
    }
}

impl ToTokens for P<ast::Expr> {
    fn to_tokens(&self, _cx: &ExtCtxt) -> Vec<TokenTree> {
        vec![ast::TtToken(self.span, token::Interpolated(token::NtExpr(self.clone())))]
    }
}

impl ToTokens for P<ast::Pat> {
    fn to_tokens(&self, _cx: &ExtCtxt) -> Vec<TokenTree> {
        vec![ast::TtToken(self.span, token::Interpolated(token::NtPat(self.clone())))]
    }
}

impl ToTokens for ast::Arm {
    fn to_tokens(&self, _cx: &ExtCtxt) -> Vec<TokenTree> {
        vec![ast::TtToken(DUMMY_SP, token::Interpolated(token::NtArm(self.clone())))]
    }
}

macro_rules! impl_to_tokens_slice {
    ($t: ty, $sep: expr) => {
        impl ToTokens for [$t] {
            fn to_tokens(&self, cx: &ExtCtxt) -> Vec<TokenTree> {
                let mut v = vec![];
                for (i, x) in self.iter().enumerate() {
                    if i > 0 {
                        v.extend($sep.iter().cloned());
                    }
                    v.extend(x.to_tokens(cx));
                }
                v
            }
        }
    };
}

impl_to_tokens_slice! { ast::Ty, [ast::TtToken(DUMMY_SP, token::Comma)] }
impl_to_tokens_slice! { P<ast::Item>, [] }

impl ToTokens for P<ast::MetaItem> {
    fn to_tokens(&self, _cx: &ExtCtxt) -> Vec<TokenTree> {
        vec![ast::TtToken(DUMMY_SP, token::Interpolated(token::NtMeta(self.clone())))]
    }
}

impl ToTokens for ast::Attribute {
    fn to_tokens(&self, cx: &ExtCtxt) -> Vec<TokenTree> {
        let mut r = vec![];
        // FIXME: The spans could be better
        r.push(ast::TtToken(self.span, token::Pound));
        if self.node.style == ast::AttrInner {
            r.push(ast::TtToken(self.span, token::Not));
        }
        r.push(ast::TtDelimited(self.span, Rc::new(ast::Delimited {
            delim: token::Bracket,
            open_span: self.span,
            tts: self.node.value.to_tokens(cx),
            close_span: self.span,
        })));
        r
    }
}

impl ToTokens for str {
    fn to_tokens(&self, cx: &ExtCtxt) -> Vec<TokenTree> {
        let lit = ast::LitStr(
            token::intern_and_get_ident(self), ast::CookedStr);
        dummy_spanned(lit).to_tokens(cx)
    }
}

impl ToTokens for () {
    fn to_tokens(&self, _cx: &ExtCtxt) -> Vec<TokenTree> {
        vec![ast::TtDelimited(DUMMY_SP, Rc::new(ast::Delimited {
            delim: token::Paren,
            open_span: DUMMY_SP,
            tts: vec![],
            close_span: DUMMY_SP,
        }))]
    }
}

impl ToTokens for ast::Lit {
    fn to_tokens(&self, cx: &ExtCtxt) -> Vec<TokenTree> {
        // FIXME: This is wrong
        P(ast::Expr {
            id: ast::DUMMY_NODE_ID,
            node: ast::ExprLit(P(self.clone())),
            span: DUMMY_SP,
        }).to_tokens(cx)
    }
}

impl ToTokens for bool {
    fn to_tokens(&self, cx: &ExtCtxt) -> Vec<TokenTree> {
        dummy_spanned(ast::LitBool(*self)).to_tokens(cx)
    }
}

impl ToTokens for char {
    fn to_tokens(&self, cx: &ExtCtxt) -> Vec<TokenTree> {
        dummy_spanned(ast::LitChar(*self)).to_tokens(cx)
    }
}

macro_rules! impl_to_tokens_int {
    (signed, $t:ty, $tag:expr) => (
        impl ToTokens for $t {
            fn to_tokens(&self, cx: &ExtCtxt) -> Vec<TokenTree> {
                let lit = ast::LitInt(*self as u64, ast::SignedIntLit($tag,
                                                                      ast::Sign::new(*self)));
                dummy_spanned(lit).to_tokens(cx)
            }
        }
    );
    (unsigned, $t:ty, $tag:expr) => (
        impl ToTokens for $t {
            fn to_tokens(&self, cx: &ExtCtxt) -> Vec<TokenTree> {
                let lit = ast::LitInt(*self as u64, ast::UnsignedIntLit($tag));
                dummy_spanned(lit).to_tokens(cx)
            }
        }
    );
}

impl_to_tokens_int! { signed, isize, ast::TyIs }
impl_to_tokens_int! { signed, i8,  ast::TyI8 }
impl_to_tokens_int! { signed, i16, ast::TyI16 }
impl_to_tokens_int! { signed, i32, ast::TyI32 }
impl_to_tokens_int! { signed, i64, ast::TyI64 }

impl_to_tokens_int! { unsigned, usize, ast::TyUs }
impl_to_tokens_int! { unsigned, u8,   ast::TyU8 }
impl_to_tokens_int! { unsigned, u16,  ast::TyU16 }
impl_to_tokens_int! { unsigned, u32,  ast::TyU32 }
impl_to_tokens_int! { unsigned, u64,  ast::TyU64 }

pub trait ExtParseUtils {
    fn parse_item(&self, s: String) -> P<ast::Item>;
    fn parse_expr(&self, s: String) -> P<ast::Expr>;
    fn parse_stmt(&self, s: String) -> P<ast::Stmt>;
    fn parse_tts(&self, s: String) -> Vec<ast::TokenTree>;
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
                                          self.parse_sess()).expect("parse error")
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
