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

extern crate syntax;
extern crate rustc;
extern crate aster;

use syntax::ast;
use syntax::codemap::Span;
use syntax::ext::base::ExtCtxt;
use syntax::ext::base;
use syntax::parse::token::*;
use syntax::parse::token;
use syntax::ptr::P;

use rustc::plugin::Registry;

///  Quasiquoting works via token trees.
///
///  This is registered as a set of expression syntax extension called quote!
///  that lifts its argument token-tree to an AST representing the
///  construction of the same token tree, with token::SubstNt interpreted
///  as antiquotes (splices).

pub fn expand_quote_tokens<'cx>(
    cx: &'cx mut ExtCtxt,
    sp: Span,
    tts: &[ast::TokenTree],
) -> Box<base::MacResult+'cx> {
    let (cx_expr, expr) = expand_tts(cx, sp, tts);
    let expanded = expand_wrapper(sp, cx_expr, expr);
    base::MacEager::expr(expanded)
}

pub fn expand_quote_ty(cx: &mut ExtCtxt,
                       sp: Span,
                       tts: &[ast::TokenTree])
                       -> Box<base::MacResult+'static> {
    let expanded = expand_parse_call(cx, sp, "parse_ty", vec!(), tts);
    base::MacEager::expr(expanded)
}

pub fn expand_quote_expr<'cx>(cx: &'cx mut ExtCtxt,
                              sp: Span,
                              tts: &[ast::TokenTree])
                              -> Box<base::MacResult+'cx> {
    let expanded = expand_parse_call(cx, sp, "parse_expr", Vec::new(), tts);
    base::MacEager::expr(expanded)
}

pub fn expand_quote_stmt(cx: &mut ExtCtxt,
                         sp: Span,
                         tts: &[ast::TokenTree])
                         -> Box<base::MacResult+'static> {
    let builder = aster::AstBuilder::new().span(sp);

    let e_attrs = builder.expr().call()
        .path().global().ids(&["std", "vec", "Vec", "new"]).build()
        .build();

    let expanded = expand_parse_call(cx, sp, "parse_stmt",
                                    vec!(e_attrs), tts);

    base::MacEager::expr(expanded)
}

pub fn expand_quote_pat<'cx>(cx: &'cx mut ExtCtxt,
                             sp: Span,
                             tts: &[ast::TokenTree])
                             -> Box<base::MacResult+'cx> {
    let expanded = expand_parse_call(cx, sp, "parse_pat", vec!(), tts);
    base::MacEager::expr(expanded)
}

pub fn expand_quote_arm(cx: &mut ExtCtxt,
                        sp: Span,
                        tts: &[ast::TokenTree])
                        -> Box<base::MacResult+'static> {
    let expanded = expand_parse_call(cx, sp, "parse_arm", vec!(), tts);
    base::MacEager::expr(expanded)
}

pub fn expand_quote_block<'cx>(cx: &'cx mut ExtCtxt,
                              sp: Span,
                              tts: &[ast::TokenTree])
                              -> Box<base::MacResult+'cx> {
    let expanded = expand_parse_call(cx, sp, "parse_block", Vec::new(), tts);
    base::MacEager::expr(expanded)
}

pub fn expand_quote_method(cx: &mut ExtCtxt,
                           sp: Span,
                           tts: &[ast::TokenTree])
                           -> Box<base::MacResult+'static> {
    let expanded = expand_parse_call(cx, sp, "parse_method_with_outer_attributes",
                                     vec!(), tts);
    base::MacEager::expr(expanded)
}

pub fn expand_quote_item<'cx>(cx: &mut ExtCtxt,
                              sp: Span,
                              tts: &[ast::TokenTree])
                              -> Box<base::MacResult+'cx> {
    let expanded = expand_parse_call(cx, sp, "parse_item_with_outer_attributes",
                                    vec!(), tts);
    base::MacEager::expr(expanded)
}

// Lift an ident to the expr that evaluates to that ident.
fn mk_ident(builder: &aster::AstBuilder, ident: ast::Ident) -> P<ast::Expr> {
    builder.expr().method_call("ident_of").id("ext_cx")
        .arg().str(ident)
        .build()
}

// Lift a name to the expr that evaluates to that name
fn mk_name<T>(builder: &aster::AstBuilder, name: T) -> P<ast::Expr>
    where T: aster::str::ToInternedString,
{
    builder.expr().method_call("name_of").id("ext_cx")
        .arg().str(name)
        .build()
}

fn mk_ast_path(builder: &aster::AstBuilder, name: &str) -> P<ast::Expr> {
    builder.expr().path()
        .global()
        .ids(&["syntax", "ast", name])
        .build()
}

fn mk_token_path(builder: &aster::AstBuilder, name: &str) -> P<ast::Expr> {
    builder.expr().path()
        .global()
        .ids(&["syntax", "parse", "token", name])
        .build()
}

fn mk_binop(builder: &aster::AstBuilder, bop: token::BinOpToken) -> P<ast::Expr> {
    let name = match bop {
        token::Plus     => "Plus",
        token::Minus    => "Minus",
        token::Star     => "Star",
        token::Slash    => "Slash",
        token::Percent  => "Percent",
        token::Caret    => "Caret",
        token::And      => "And",
        token::Or       => "Or",
        token::Shl      => "Shl",
        token::Shr      => "Shr"
    };
    mk_token_path(builder, name)
}

fn mk_delim(builder: &aster::AstBuilder, delim: token::DelimToken) -> P<ast::Expr> {
    let name = match delim {
        token::Paren     => "Paren",
        token::Bracket   => "Bracket",
        token::Brace     => "Brace",
    };
    mk_token_path(builder, name)
}

#[allow(non_upper_case_globals)]
fn mk_token(builder: &aster::AstBuilder, tok: &token::Token) -> P<ast::Expr> {
    macro_rules! mk_lit {
        ($name: expr, $suffix: expr, $($args: expr),+) => {{
            let inner = builder.expr().call()
                .build(mk_token_path(builder, $name))
                $(.with_arg($args))+
                .build();

            let suffix = match $suffix {
                Some(name) => builder.expr().some().build(mk_name(builder, name)),
                None => builder.expr().none(),
            };

            builder.expr().call()
                .build(mk_token_path(builder, "Literal"))
                .with_arg(inner)
                .with_arg(suffix)
                .build()
        }}
    }

    match *tok {
        token::BinOp(binop) => {
            builder.expr().call()
                .build(mk_token_path(builder, "BinOp"))
                .with_arg(mk_binop(builder, binop))
                .build()
        }
        token::BinOpEq(binop) => {
            builder.expr().call()
                .build(mk_token_path(builder, "BinOpEq"))
                .with_arg(mk_binop(builder, binop))
                .build()
        }

        token::OpenDelim(delim) => {
            builder.expr().call()
                .build(mk_token_path(builder, "OpenDelim"))
                .with_arg(mk_delim(builder, delim))
                .build()
        }
        token::CloseDelim(delim) => {
            builder.expr().call()
                .build(mk_token_path(builder, "CloseDelim"))
                .with_arg(mk_delim(builder, delim))
                .build()
        }

        token::Literal(token::Byte(i), suf) => {
            let e_byte = mk_name(builder, i.ident());
            mk_lit!("Byte", suf, e_byte)
        }

        token::Literal(token::Char(i), suf) => {
            let e_char = mk_name(builder, i.ident());
            mk_lit!("Char", suf, e_char)
        }

        token::Literal(token::Integer(i), suf) => {
            let e_int = mk_name(builder, i.ident());
            mk_lit!("Integer", suf, e_int)
        }

        token::Literal(token::Float(fident), suf) => {
            let e_fident = mk_name(builder, fident.ident());
            mk_lit!("Float", suf, e_fident)
        }

        token::Literal(token::Binary(ident), suf) => {
            mk_lit!("Binary", suf, mk_name(builder, ident.ident()))
        }

        token::Literal(token::BinaryRaw(ident, n), suf) => {
            mk_lit!(
                "BinaryRaw",
                suf,
                mk_name(builder, ident.ident()),
                builder.expr().usize(n))
        }

        token::Literal(token::Str_(ident), suf) => {
            mk_lit!("Str_", suf, mk_name(builder, ident.ident()))
        }

        token::Literal(token::StrRaw(ident, n), suf) => {
            mk_lit!(
                "StrRaw",
                suf,
                mk_name(builder, ident.ident()),
                builder.expr().usize(n))
        }

        token::Ident(ident, style) => {
            let style = match style {
                ModName => mk_token_path(builder, "ModName"),
                Plain   => mk_token_path(builder, "Plain"),
            };

            builder.expr().call()
                .build(mk_token_path(builder, "Ident"))
                .with_arg(mk_ident(builder, ident))
                .with_arg(style)
                .build()
        }

        token::Lifetime(ident) => {
            builder.expr().call()
                .build(mk_token_path(builder, "Lifetime"))
                .with_arg(mk_ident(builder, ident))
                .build()
        }

        token::DocComment(ident) => {
            builder.expr().call()
                .build(mk_token_path(builder, "DocComment"))
                .with_arg(mk_name(builder, ident))
                .build()
        }

        token::Eq           => mk_token_path(builder, "Eq"),
        token::Lt           => mk_token_path(builder, "Lt"),
        token::Le           => mk_token_path(builder, "Le"),
        token::EqEq         => mk_token_path(builder, "EqEq"),
        token::Ne           => mk_token_path(builder, "Ne"),
        token::Ge           => mk_token_path(builder, "Ge"),
        token::Gt           => mk_token_path(builder, "Gt"),
        token::AndAnd       => mk_token_path(builder, "AndAnd"),
        token::OrOr         => mk_token_path(builder, "OrOr"),
        token::Not          => mk_token_path(builder, "Not"),
        token::Tilde        => mk_token_path(builder, "Tilde"),
        token::At           => mk_token_path(builder, "At"),
        token::Dot          => mk_token_path(builder, "Dot"),
        token::DotDot       => mk_token_path(builder, "DotDot"),
        token::Comma        => mk_token_path(builder, "Comma"),
        token::Semi         => mk_token_path(builder, "Semi"),
        token::Colon        => mk_token_path(builder, "Colon"),
        token::ModSep       => mk_token_path(builder, "ModSep"),
        token::RArrow       => mk_token_path(builder, "RArrow"),
        token::LArrow       => mk_token_path(builder, "LArrow"),
        token::FatArrow     => mk_token_path(builder, "FatArrow"),
        token::Pound        => mk_token_path(builder, "Pound"),
        token::Dollar       => mk_token_path(builder, "Dollar"),
        token::Underscore   => mk_token_path(builder, "Underscore"),
        token::Eof          => mk_token_path(builder, "Eof"),
        token::DotDotDot    => mk_token_path(builder, "DotDotDot"),
        token::Question     => mk_token_path(builder, "Question"),
        token::Whitespace   => mk_token_path(builder, "Whitespace"),
        token::Comment      => mk_token_path(builder, "Comment"),

        token::Shebang(s) => {
            builder.expr().call()
                .build(mk_token_path(builder, "Shebang"))
                .arg().str(s)
                .build()
        }

        token::Interpolated(..)
        | token::MatchNt(..)
        | token::SubstNt(..)
        | token::SpecialVarNt(..) => {
            panic!("quote! with {:?} token", tok)
        }
    }
}

fn mk_tt(tt: &ast::TokenTree) -> Vec<P<ast::Stmt>> {
    let builder = aster::AstBuilder::new();

    match *tt {
        ast::TtToken(sp, SubstNt(ident, _)) => {
            // tt.extend($ident.to_tokens(ext_cx).into_iter())

            let builder = builder.clone().span(sp);

            let e_to_toks = builder.expr().method_call("to_tokens")
                .id(ident)
                .arg().id("ext_cx")
                .build();

            let e_to_toks = builder.expr().method_call("into_iter")
                .build(e_to_toks)
                .build();

            let e_push = builder.expr().method_call("extend")
                .id("tt")
                .with_arg(e_to_toks)
                .build();

            vec![builder.stmt().build_expr(e_push)]
        }
        ref tt @ ast::TtToken(_, MatchNt(..)) => {
            let mut seq = vec![];
            for i in 0..tt.len() {
                seq.push(tt.get_tt(i));
            }
            mk_tts(&seq[..])
        }
        ast::TtToken(sp, ref tok) => {
            let builder = builder.clone().span(sp);

            let e_tok = builder.expr().call()
                .build(mk_ast_path(&builder, "TtToken"))
                .arg().id("_sp")
                .with_arg(mk_token(&builder, tok))
                .build();

            let e_push = builder.expr().method_call("push")
                .id("tt")
                .with_arg(e_tok)
                .build();

            vec![builder.stmt().build_expr(e_push)]
        },
        ast::TtDelimited(_, ref delimed) => {
            mk_tt(
                &delimed.open_tt(),
            ).into_iter()
                .chain(delimed.tts.iter().flat_map(|tt| mk_tt(tt).into_iter()))
                .chain(mk_tt(&delimed.close_tt()).into_iter())
                .collect()
        },
        ast::TtSequence(..) => panic!("TtSequence in quote!"),
    }
}

fn mk_tts(tts: &[ast::TokenTree]) -> Vec<P<ast::Stmt>> {
    let mut ss = Vec::new();
    for tt in tts {
        ss.extend(mk_tt(tt).into_iter());
    }
    ss
}

fn expand_tts(cx: &ExtCtxt, sp: Span, tts: &[ast::TokenTree])
              -> (P<ast::Expr>, P<ast::Expr>) {
    // NB: It appears that the main parser loses its mind if we consider
    // $foo as a TtNonterminal during the main parse, so we have to re-parse
    // under quote_depth > 0. This is silly and should go away; the _guess_ is
    // it has to do with transition away from supporting old-style macros, so
    // try removing it when enough of them are gone.

    let mut p = cx.new_parser_from_tts(tts);
    p.quote_depth += 1;

    let cx_expr = p.parse_expr();
    if !p.eat(&token::Comma) {
        p.fatal("expected token `,`");
    }

    let tts = p.parse_all_token_trees();
    p.abort_if_errors();

    // We also bind a single value, sp, to ext_cx.call_site()
    //
    // This causes every span in a token-tree quote to be attributed to the
    // call site of the extension using the quote. We can't really do much
    // better since the source of the quote may well be in a library that
    // was not even parsed by this compilation run, that the user has no
    // source code for (eg. in libsyntax, which they're just _using_).
    //
    // The old quasiquoter had an elaborate mechanism for denoting input
    // file locations from which quotes originated; unfortunately this
    // relied on feeding the source string of the quote back into the
    // compiler (which we don't really want to do) and, in any case, only
    // pushed the problem a very small step further back: an error
    // resulting from a parse of the resulting quote is still attributed to
    // the site the string literal occurred, which was in a source file
    // _other_ than the one the user has control over. For example, an
    // error in a quote from the protocol compiler, invoked in user code
    // using macro_rules! for example, will be attributed to the macro_rules.rs
    // file in libsyntax, which the user might not even have source to (unless
    // they happen to have a compiler on hand). Over all, the phase distinction
    // just makes quotes "hard to attribute". Possibly this could be fixed
    // by recreating some of the original qq machinery in the tt regime
    // (pushing fake FileMaps onto the parser to account for original sites
    // of quotes, for example) but at this point it seems not likely to be
    // worth the hassle.

    let builder = aster::AstBuilder::new().span(sp);

    let e_sp = builder.expr().method_call("call_site")
        .id("ext_cx")
        .build();

    let stmt_let_sp = builder.stmt()
        .let_id("_sp").build(e_sp);

    let stmt_let_tt = builder.stmt().let_().mut_id("tt")
        .expr().call()
            .path().global().ids(&["std", "vec", "Vec", "new"]).build()
            .build();

    let block = builder.expr().block()
        .with_stmt(stmt_let_sp)
        .with_stmt(stmt_let_tt)
        .with_stmts(mk_tts(&tts))
        .expr().id("tt");

    (cx_expr, block)
}

fn expand_wrapper(sp: Span,
                  cx_expr: P<ast::Expr>,
                  expr: P<ast::Expr>) -> P<ast::Expr> {
    let builder = aster::AstBuilder::new().span(sp);

    // Explicitly borrow to avoid moving from the invoker (#16992)
    let cx_expr_borrow = builder.expr()
        .addr_of().build_deref(cx_expr);

    let stmt_let_ext_cx = builder.stmt().let_id("ext_cx")
        .build(cx_expr_borrow);

    let use_quote = builder.item()
        .attr().build_allow(&["unused_imports"])
        .use_glob()
        .id("quasi")
        .build();

    builder.expr().block()
        .stmt().build_item(use_quote)
        .with_stmt(stmt_let_ext_cx)
        .build_expr(expr)
}

fn expand_parse_call(cx: &ExtCtxt,
                     sp: Span,
                     parse_method: &str,
                     arg_exprs: Vec<P<ast::Expr>> ,
                     tts: &[ast::TokenTree]) -> P<ast::Expr> {
    let builder = aster::AstBuilder::new().span(sp);

    let (cx_expr, tts_expr) = expand_tts(cx, sp, tts);

    let cfg_call = builder.expr().method_call("cfg")
        .id("ext_cx")
        .build();

    let parse_sess_call = builder.expr().method_call("parse_sess")
        .id("ext_cx")
        .build();

    let new_parser_call = builder.expr().call()
        .id("new_parser_from_tts")
        .with_arg(parse_sess_call)
        .with_arg(cfg_call)
        .with_arg(tts_expr)
        .build();

    let expr = builder.expr().method_call(parse_method)
        .build(new_parser_call)
        .with_args(arg_exprs)
        .build();

    expand_wrapper(sp, cx_expr, expr)
}

#[plugin_registrar]
#[doc(hidden)]
pub fn plugin_registrar(reg: &mut Registry) {
    reg.register_macro("quote_tokens", expand_quote_tokens);
    reg.register_macro("quote_ty", expand_quote_ty);
    reg.register_macro("quote_expr", expand_quote_expr);
    reg.register_macro("quote_stmt", expand_quote_stmt);
    reg.register_macro("quote_pat", expand_quote_pat);
    reg.register_macro("quote_arm", expand_quote_arm);
    reg.register_macro("quote_block", expand_quote_block);
    reg.register_macro("quote_method", expand_quote_method);
    reg.register_macro("quote_item", expand_quote_item);
}
