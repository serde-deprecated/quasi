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

extern crate "syntax_ast_builder" as builder;

use syntax::ast;
use syntax::codemap::{Span, respan};
use syntax::ext::base::ExtCtxt;
use syntax::ext::base;
use syntax::ext::build::AstBuilder;
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
    let expanded = expand_wrapper(cx, sp, cx_expr, expr);
    base::MacExpr::new(expanded)
}

pub fn expand_quote_expr<'cx>(cx: &'cx mut ExtCtxt,
                              sp: Span,
                              tts: &[ast::TokenTree])
                              -> Box<base::MacResult+'cx> {
    let expanded = expand_parse_call(cx, sp, "parse_expr", Vec::new(), tts);
    base::MacExpr::new(expanded)
}

pub fn expand_quote_item<'cx>(cx: &mut ExtCtxt,
                              sp: Span,
                              tts: &[ast::TokenTree])
                              -> Box<base::MacResult+'cx> {
    let expanded = expand_parse_call(cx, sp, "parse_item_with_outer_attributes",
                                    vec!(), tts);
    base::MacExpr::new(expanded)
}

pub fn expand_quote_pat<'cx>(cx: &'cx mut ExtCtxt,
                             sp: Span,
                             tts: &[ast::TokenTree])
                             -> Box<base::MacResult+'cx> {
    let expanded = expand_parse_call(cx, sp, "parse_pat", vec!(), tts);
    base::MacExpr::new(expanded)
}

pub fn expand_quote_arm(cx: &mut ExtCtxt,
                        sp: Span,
                        tts: &[ast::TokenTree])
                        -> Box<base::MacResult+'static> {
    let expanded = expand_parse_call(cx, sp, "parse_arm", vec!(), tts);
    base::MacExpr::new(expanded)
}

pub fn expand_quote_ty(cx: &mut ExtCtxt,
                       sp: Span,
                       tts: &[ast::TokenTree])
                       -> Box<base::MacResult+'static> {
    let expanded = expand_parse_call(cx, sp, "parse_ty", vec!(), tts);
    base::MacExpr::new(expanded)
}

pub fn expand_quote_method(cx: &mut ExtCtxt,
                           sp: Span,
                           tts: &[ast::TokenTree])
                           -> Box<base::MacResult+'static> {
    let expanded = expand_parse_call(cx, sp, "parse_method_with_outer_attributes",
                                     vec!(), tts);
    base::MacExpr::new(expanded)
}

pub fn expand_quote_stmt(cx: &mut ExtCtxt,
                         sp: Span,
                         tts: &[ast::TokenTree])
                         -> Box<base::MacResult+'static> {
    let e_attrs = cx.expr_vec_ng(sp);
    let expanded = expand_parse_call(cx, sp, "parse_stmt",
                                    vec!(e_attrs), tts);
    base::MacExpr::new(expanded)
}

fn id_ext(str: &str) -> ast::Ident {
    str_to_ident(str)
}

// Lift an ident to the expr that evaluates to that ident.
fn mk_ident(builder: &builder::AstBuilder, sp: Span, ident: ast::Ident) -> P<ast::Expr> {
    builder.expr().span(sp).method_call("ident_of").id("ext_cx")
        .arg().str(ident)
        .build()
}

// Lift a name to the expr that evaluates to that name
fn mk_name(builder: &builder::AstBuilder, sp: Span, ident: ast::Ident) -> P<ast::Expr> {
    builder.expr().span(sp).method_call("name_of").id("ext_cx")
        .arg().str(ident)
        .build()
}

fn mk_ast_path(builder: &builder::AstBuilder, sp: Span, name: &str) -> P<ast::Expr> {
    builder.expr().span(sp).path().global()
        .build_from_ids(&["syntax", "ast", name])
}

fn mk_token_path(builder: &builder::AstBuilder, sp: Span, name: &str) -> P<ast::Expr> {
    builder.expr().span(sp).path().global()
        .build_from_ids(&["syntax", "parse", "token", name])
}

fn mk_binop(builder: &builder::AstBuilder, sp: Span, bop: token::BinOpToken) -> P<ast::Expr> {
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
    mk_token_path(builder, sp, name)
}

fn mk_delim(builder: &builder::AstBuilder, sp: Span, delim: token::DelimToken) -> P<ast::Expr> {
    let name = match delim {
        token::Paren     => "Paren",
        token::Bracket   => "Bracket",
        token::Brace     => "Brace",
    };
    mk_token_path(builder, sp, name)
}

#[allow(non_upper_case_globals)]
fn mk_token(cx: &ExtCtxt, sp: Span, tok: &token::Token) -> P<ast::Expr> {
    let ctx = builder::Ctx::new();
    let builder = builder::AstBuilder::new(&ctx);

    macro_rules! mk_lit {
        ($name: expr, $suffix: expr, $($args: expr),*) => {{
            let inner = cx.expr_call(
                sp,
                mk_token_path(&builder, sp, $name),
                vec![$($args),*]);

            let suffix = match $suffix {
                Some(name) => {
                    cx.expr_some(
                        sp,
                        mk_name(&builder, sp, ast::Ident::new(name)))
                }
                None => {
                    cx.expr_none(sp)
                }
            };

            cx.expr_call(
                sp,
                mk_token_path(&builder, sp, "Literal"),
                vec![inner, suffix])
        }}
    }

    match *tok {
        token::BinOp(binop) => {
            cx.expr_call(
                sp,
                mk_token_path(&builder, sp, "BinOp"),
                vec!(mk_binop(&builder, sp, binop)))
        }
        token::BinOpEq(binop) => {
            cx.expr_call(
                sp,
                mk_token_path(&builder, sp, "BinOpEq"),
                vec!(mk_binop(&builder, sp, binop)))
        }

        token::OpenDelim(delim) => {
            cx.expr_call(
                sp,
                mk_token_path(&builder, sp, "OpenDelim"),
                vec![mk_delim(&builder, sp, delim)])
        }
        token::CloseDelim(delim) => {
            cx.expr_call(
                sp,
                mk_token_path(&builder, sp, "CloseDelim"),
                vec![mk_delim(&builder, sp, delim)])
        }

        token::Literal(token::Byte(i), suf) => {
            let e_byte = mk_name(&builder, sp, i.ident());
            mk_lit!("Byte", suf, e_byte)
        }

        token::Literal(token::Char(i), suf) => {
            let e_char = mk_name(&builder, sp, i.ident());
            mk_lit!("Char", suf, e_char)
        }

        token::Literal(token::Integer(i), suf) => {
            let e_int = mk_name(&builder, sp, i.ident());
            mk_lit!("Integer", suf, e_int)
        }

        token::Literal(token::Float(fident), suf) => {
            let e_fident = mk_name(&builder, sp, fident.ident());
            mk_lit!("Float", suf, e_fident)
        }

        token::Literal(token::Str_(ident), suf) => {
            mk_lit!("Str_", suf, mk_name(&builder, sp, ident.ident()))
        }

        token::Literal(token::StrRaw(ident, n), suf) => {
            mk_lit!(
                "StrRaw",
                suf,
                mk_name(&builder, sp, ident.ident()), cx.expr_usize(sp, n))
        }

        token::Ident(ident, style) => {
            cx.expr_call(
                sp,
                mk_token_path(&builder, sp, "Ident"),
                vec![mk_ident(&builder, sp, ident),
                match style {
                    ModName => mk_token_path(&builder, sp, "ModName"),
                    Plain   => mk_token_path(&builder, sp, "Plain"),
                }])
        }

        token::Lifetime(ident) => {
            cx.expr_call(
                sp,
                mk_token_path(&builder, sp, "Lifetime"),
                vec!(mk_ident(&builder, sp, ident)))
        }

        token::DocComment(ident) => {
            cx.expr_call(
                sp,
                mk_token_path(&builder, sp, "DocComment"),
                vec!(mk_name(&builder, sp, ident.ident())))
        }

        token::Eq           => mk_token_path(&builder, sp, "Eq"),
        token::Lt           => mk_token_path(&builder, sp, "Lt"),
        token::Le           => mk_token_path(&builder, sp, "Le"),
        token::EqEq         => mk_token_path(&builder, sp, "EqEq"),
        token::Ne           => mk_token_path(&builder, sp, "Ne"),
        token::Ge           => mk_token_path(&builder, sp, "Ge"),
        token::Gt           => mk_token_path(&builder, sp, "Gt"),
        token::AndAnd       => mk_token_path(&builder, sp, "AndAnd"),
        token::OrOr         => mk_token_path(&builder, sp, "OrOr"),
        token::Not          => mk_token_path(&builder, sp, "Not"),
        token::Tilde        => mk_token_path(&builder, sp, "Tilde"),
        token::At           => mk_token_path(&builder, sp, "At"),
        token::Dot          => mk_token_path(&builder, sp, "Dot"),
        token::DotDot       => mk_token_path(&builder, sp, "DotDot"),
        token::Comma        => mk_token_path(&builder, sp, "Comma"),
        token::Semi         => mk_token_path(&builder, sp, "Semi"),
        token::Colon        => mk_token_path(&builder, sp, "Colon"),
        token::ModSep       => mk_token_path(&builder, sp, "ModSep"),
        token::RArrow       => mk_token_path(&builder, sp, "RArrow"),
        token::LArrow       => mk_token_path(&builder, sp, "LArrow"),
        token::FatArrow     => mk_token_path(&builder, sp, "FatArrow"),
        token::Pound        => mk_token_path(&builder, sp, "Pound"),
        token::Dollar       => mk_token_path(&builder, sp, "Dollar"),
        token::Underscore   => mk_token_path(&builder, sp, "Underscore"),
        token::Eof          => mk_token_path(&builder, sp, "Eof"),

        _ => panic!("quote! with {:?} token", tok),
    }
}

fn mk_tt(cx: &ExtCtxt, tt: &ast::TokenTree) -> Vec<P<ast::Stmt>> {
    let ctx = builder::Ctx::new();
    let builder = builder::AstBuilder::new(&ctx);

    match *tt {
        ast::TtToken(sp, SubstNt(ident, _)) => {
            // tt.extend($ident.to_tokens(ext_cx).into_iter())

            let e_to_toks = cx.expr_method_call(
                sp,
                cx.expr_ident(sp, ident),
                id_ext("to_tokens"),
                vec!(cx.expr_ident(sp, id_ext("ext_cx"))));

            let e_to_toks = cx.expr_method_call(
                sp,
                e_to_toks,
                id_ext("into_iter"), vec![]);

            let e_push = cx.expr_method_call(
                sp,
                cx.expr_ident(sp, id_ext("tt")),
                id_ext("extend"),
                vec!(e_to_toks));

            vec!(cx.stmt_expr(e_push))
        }
        ref tt @ ast::TtToken(_, MatchNt(..)) => {
            let mut seq = vec![];
            for i in 0..tt.len() {
                seq.push(tt.get_tt(i));
            }
            mk_tts(cx, &seq[..])
        }
        ast::TtToken(sp, ref tok) => {
            let e_sp = cx.expr_ident(sp, id_ext("_sp"));

            let e_tok = cx.expr_call(
                sp,
                mk_ast_path(&builder, sp, "TtToken"),
                vec!(e_sp, mk_token(cx, sp, tok)));

            let e_push = cx.expr_method_call(
                sp,
                cx.expr_ident(sp, id_ext("tt")),
                id_ext("push"),
                vec!(e_tok));

            vec!(cx.stmt_expr(e_push))
        },
        ast::TtDelimited(_, ref delimed) => {
            mk_tt(
                cx,
                &delimed.open_tt(),
            ).into_iter()
                .chain(delimed.tts.iter().flat_map(|tt| mk_tt(cx, tt).into_iter()))
                .chain(mk_tt(cx, &delimed.close_tt()).into_iter())
                .collect()
        },
        ast::TtSequence(..) => panic!("TtSequence in quote!"),
    }
}

fn mk_tts(cx: &ExtCtxt, tts: &[ast::TokenTree]) -> Vec<P<ast::Stmt>> {
    let mut ss = Vec::new();
    for tt in tts {
        ss.extend(mk_tt(cx, tt).into_iter());
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

    let e_sp = cx.expr_method_call(sp,
                                   cx.expr_ident(sp, id_ext("ext_cx")),
                                   id_ext("call_site"),
                                   Vec::new());

    let stmt_let_sp = cx.stmt_let(sp, false,
                                  id_ext("_sp"),
                                  e_sp);

    let stmt_let_tt = cx.stmt_let(sp, true, id_ext("tt"), cx.expr_vec_ng(sp));

    let mut vector = vec!(stmt_let_sp, stmt_let_tt);
    vector.extend(mk_tts(cx, &tts[..]).into_iter());
    let block = cx.expr_block(
        cx.block_all(sp,
                     vector,
                     Some(cx.expr_ident(sp, id_ext("tt")))));

    (cx_expr, block)
}

fn expand_wrapper(cx: &ExtCtxt,
                  sp: Span,
                  cx_expr: P<ast::Expr>,
                  expr: P<ast::Expr>) -> P<ast::Expr> {
    // Explicitly borrow to avoid moving from the invoker (#16992)
    let cx_expr_borrow = cx.expr_addr_of(sp, cx.expr_deref(sp, cx_expr));
    let stmt_let_ext_cx = cx.stmt_let(sp, false, id_ext("ext_cx"), cx_expr_borrow);

    let ignore_unused_import = cx.meta_list(
        sp,
        InternedString::new("allow"),
        vec![cx.meta_word(sp, InternedString::new("unused_imports"))]
    );

    let quote_path = cx.path(sp, vec![cx.ident_of("quote")]);
    let use_quote = P(ast::Item {
        id: ast::DUMMY_NODE_ID,
        ident: special_idents::invalid,
        attrs: vec![cx.attribute(sp, ignore_unused_import)],
        node: ast::ItemUse(
            P(respan(sp, ast::ViewPathGlob(quote_path))),
        ),
        vis: ast::Inherited,
        span: sp,
    });

    let stmts = vec![
        cx.stmt_item(sp, use_quote),
        stmt_let_ext_cx,
    ];

    cx.expr_block(cx.block_all(sp, stmts, Some(expr)))
}

fn expand_parse_call(cx: &ExtCtxt,
                     sp: Span,
                     parse_method: &str,
                     arg_exprs: Vec<P<ast::Expr>> ,
                     tts: &[ast::TokenTree]) -> P<ast::Expr> {
    let (cx_expr, tts_expr) = expand_tts(cx, sp, tts);

    let cfg_call = || cx.expr_method_call(
        sp, cx.expr_ident(sp, id_ext("ext_cx")),
        id_ext("cfg"), Vec::new());

    let parse_sess_call = || cx.expr_method_call(
        sp, cx.expr_ident(sp, id_ext("ext_cx")),
        id_ext("parse_sess"), Vec::new());

    let new_parser_call =
        cx.expr_call(sp,
                     cx.expr_ident(sp, id_ext("new_parser_from_tts")),
                     vec!(parse_sess_call(), cfg_call(), tts_expr));

    let expr = cx.expr_method_call(sp, new_parser_call, id_ext(parse_method),
                                   arg_exprs);

    expand_wrapper(cx, sp, cx_expr, expr)
}

#[plugin_registrar]
#[doc(hidden)]
pub fn plugin_registrar(reg: &mut Registry) {
    reg.register_macro("quote_tokens", expand_quote_tokens);
    reg.register_macro("quote_expr", expand_quote_expr);
    reg.register_macro("quote_item", expand_quote_item);
    reg.register_macro("quote_pat", expand_quote_pat);
    reg.register_macro("quote_arm", expand_quote_arm);
    reg.register_macro("quote_ty", expand_quote_ty);
    reg.register_macro("quote_method", expand_quote_method);
    reg.register_macro("quote_stmt", expand_quote_stmt);
}
