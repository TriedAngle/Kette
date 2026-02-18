use std::collections::{BTreeMap, HashSet};

use parser::ast::Expr;
use parser::ast::ExprKind;
use parser::token::{Token, TokenKind};
use parser::{Lexer, Parser};
use tower_lsp::lsp_types::{
    SemanticToken, SemanticTokenModifier, SemanticTokenType,
};

use crate::position::byte_offset_to_position;

const TYPE_UNARY_METHOD: u32 = 0;
const TYPE_KEYWORD_MESSAGE: u32 = 1;
const TYPE_LOCAL: u32 = 2;
const TYPE_GLOBAL: u32 = 3;
const TYPE_OPERATOR: u32 = 4;
const TYPE_LITERAL_NUMBER: u32 = 5;
const TYPE_SELF_KEYWORD: u32 = 6;

pub fn token_types() -> Vec<SemanticTokenType> {
    vec![
        SemanticTokenType::METHOD,
        SemanticTokenType::FUNCTION,
        SemanticTokenType::VARIABLE,
        SemanticTokenType::NAMESPACE,
        SemanticTokenType::OPERATOR,
        SemanticTokenType::NUMBER,
        SemanticTokenType::new("selfKeyword"),
    ]
}

pub fn token_modifiers() -> Vec<SemanticTokenModifier> {
    Vec::new()
}

pub fn semantic_tokens(source: &str) -> Vec<SemanticToken> {
    let tokens: Vec<Token> = Lexer::from_str(source)
        .filter(|t| {
            !t.is_eof()
                && !t.is_comment()
                && !matches!(t.kind, TokenKind::Error(_))
        })
        .collect();

    let parse_results: Vec<_> = Parser::new(Lexer::from_str(source)).collect();
    let exprs: Vec<Expr> =
        parse_results.into_iter().filter_map(Result::ok).collect();

    let globals = collect_top_level_globals(&exprs);
    let mut classified = Classified::default();

    classify_keyword_and_operator_tokens(&tokens, &mut classified);

    let mut unary_selector_spans = HashSet::new();
    for expr in &exprs {
        collect_unary_selector_spans(
            expr,
            &tokens,
            &mut unary_selector_spans,
            &mut classified,
        );
    }

    let mut scopes = Vec::new();
    for expr in &exprs {
        classify_identifier_usage(
            expr,
            true,
            &globals,
            &mut scopes,
            &unary_selector_spans,
            &mut classified,
        );
    }

    classified.to_lsp_tokens(source)
}

#[derive(Default)]
struct Classified {
    by_span: BTreeMap<(usize, usize), u32>,
}

impl Classified {
    fn add(&mut self, start: usize, end: usize, token_type: u32) {
        if end <= start {
            return;
        }
        self.by_span.entry((start, end)).or_insert(token_type);
    }

    fn to_lsp_tokens(self, source: &str) -> Vec<SemanticToken> {
        let mut out = Vec::new();
        let mut prev_line = 0u32;
        let mut prev_start = 0u32;

        for ((start, end), token_type) in self.by_span {
            let start_pos = byte_offset_to_position(source, start);
            let end_pos = byte_offset_to_position(source, end);
            if start_pos.line != end_pos.line {
                continue;
            }
            let length = end_pos.character.saturating_sub(start_pos.character);
            if length == 0 {
                continue;
            }

            let delta_line = start_pos.line.saturating_sub(prev_line);
            let delta_start = if delta_line == 0 {
                start_pos.character.saturating_sub(prev_start)
            } else {
                start_pos.character
            };

            out.push(SemanticToken {
                delta_line,
                delta_start,
                length,
                token_type,
                token_modifiers_bitset: 0,
            });

            prev_line = start_pos.line;
            prev_start = start_pos.character;
        }

        out
    }
}

#[derive(Default)]
struct Scope {
    locals: HashSet<String>,
}

fn classify_keyword_and_operator_tokens(
    tokens: &[Token],
    out: &mut Classified,
) {
    for tok in tokens {
        match &tok.kind {
            TokenKind::Keyword(_) => {
                out.add(
                    tok.span.start.offset,
                    tok.span.end.offset,
                    TYPE_KEYWORD_MESSAGE,
                );
            }
            TokenKind::Operator(_) => {
                out.add(
                    tok.span.start.offset,
                    tok.span.end.offset,
                    TYPE_OPERATOR,
                );
            }
            TokenKind::SelfKw => {
                out.add(
                    tok.span.start.offset,
                    tok.span.end.offset,
                    TYPE_SELF_KEYWORD,
                );
            }
            _ => {}
        }
    }
}

fn collect_unary_selector_spans(
    expr: &Expr,
    tokens: &[Token],
    span_set: &mut HashSet<(usize, usize)>,
    out: &mut Classified,
) {
    match &expr.kind {
        ExprKind::UnaryMessage { receiver, selector } => {
            collect_unary_selector_spans(receiver, tokens, span_set, out);
            if let Some(span) =
                find_unary_selector_span(expr, receiver, selector, tokens)
            {
                span_set.insert(span);
                out.add(span.0, span.1, TYPE_UNARY_METHOD);
            }
        }
        ExprKind::BinaryMessage {
            receiver, argument, ..
        } => {
            collect_unary_selector_spans(receiver, tokens, span_set, out);
            collect_unary_selector_spans(argument, tokens, span_set, out);
        }
        ExprKind::KeywordMessage { receiver, pairs } => {
            collect_unary_selector_spans(receiver, tokens, span_set, out);
            for pair in pairs {
                collect_unary_selector_spans(
                    &pair.argument,
                    tokens,
                    span_set,
                    out,
                );
            }
        }
        ExprKind::Paren(inner)
        | ExprKind::Return(inner)
        | ExprKind::Resend { message: inner } => {
            collect_unary_selector_spans(inner, tokens, span_set, out);
        }
        ExprKind::DirectedResend { message, .. } => {
            collect_unary_selector_spans(message, tokens, span_set, out);
        }
        ExprKind::Block { body, .. } | ExprKind::Sequence(body) => {
            for e in body {
                collect_unary_selector_spans(e, tokens, span_set, out);
            }
        }
        ExprKind::Object { slots, body } => {
            for slot in slots {
                collect_unary_selector_spans(
                    &slot.value,
                    tokens,
                    span_set,
                    out,
                );
            }
            for e in body {
                collect_unary_selector_spans(e, tokens, span_set, out);
            }
        }
        ExprKind::Assignment { target, value, .. } => {
            collect_unary_selector_spans(target, tokens, span_set, out);
            collect_unary_selector_spans(value, tokens, span_set, out);
        }
        ExprKind::Cascade { receiver, messages } => {
            collect_unary_selector_spans(receiver, tokens, span_set, out);
            for msg in messages {
                collect_unary_selector_spans(msg, tokens, span_set, out);
            }
        }
        _ => {}
    }
}

fn find_unary_selector_span(
    expr: &Expr,
    receiver: &Expr,
    selector: &str,
    tokens: &[Token],
) -> Option<(usize, usize)> {
    for tok in tokens.iter().rev() {
        if tok.span.end.offset != expr.span.end.offset {
            continue;
        }
        if tok.span.start.offset < receiver.span.end.offset {
            continue;
        }
        if let TokenKind::Identifier(name) = &tok.kind {
            if name == selector {
                return Some((tok.span.start.offset, tok.span.end.offset));
            }
        }
    }

    for tok in tokens.iter().rev() {
        if tok.span.end.offset > expr.span.end.offset {
            continue;
        }
        if tok.span.start.offset < receiver.span.end.offset {
            continue;
        }
        if let TokenKind::Identifier(name) = &tok.kind {
            if name == selector {
                return Some((tok.span.start.offset, tok.span.end.offset));
            }
        }
    }

    None
}

fn collect_top_level_globals(exprs: &[Expr]) -> HashSet<String> {
    let mut globals = HashSet::new();
    for expr in exprs {
        if let ExprKind::Assignment { target, .. } = &expr.kind {
            if let ExprKind::Ident(name) = &target.kind {
                globals.insert(name.clone());
            }
        }
    }
    globals
}

fn classify_identifier_usage(
    expr: &Expr,
    top_level: bool,
    globals: &HashSet<String>,
    scopes: &mut Vec<Scope>,
    unary_selector_spans: &HashSet<(usize, usize)>,
    out: &mut Classified,
) {
    match &expr.kind {
        ExprKind::SelfRef => {
            out.add(
                expr.span.start.offset,
                expr.span.end.offset,
                TYPE_SELF_KEYWORD,
            );
        }
        ExprKind::Ident(name) => {
            let span = (expr.span.start.offset, expr.span.end.offset);
            if unary_selector_spans.contains(&span) {
                return;
            }
            if is_literal_ident(name) {
                out.add(span.0, span.1, TYPE_LITERAL_NUMBER);
                return;
            }
            let token_type = if is_local(name, scopes) {
                TYPE_LOCAL
            } else if top_level || globals.contains(name) {
                TYPE_GLOBAL
            } else {
                TYPE_LOCAL
            };
            out.add(span.0, span.1, token_type);
        }
        ExprKind::UnaryMessage { receiver, .. } => {
            classify_identifier_usage(
                receiver,
                top_level,
                globals,
                scopes,
                unary_selector_spans,
                out,
            );
        }
        ExprKind::BinaryMessage {
            receiver, argument, ..
        } => {
            classify_identifier_usage(
                receiver,
                top_level,
                globals,
                scopes,
                unary_selector_spans,
                out,
            );
            classify_identifier_usage(
                argument,
                top_level,
                globals,
                scopes,
                unary_selector_spans,
                out,
            );
        }
        ExprKind::KeywordMessage { receiver, pairs } => {
            classify_identifier_usage(
                receiver,
                top_level,
                globals,
                scopes,
                unary_selector_spans,
                out,
            );
            for pair in pairs {
                classify_identifier_usage(
                    &pair.argument,
                    top_level,
                    globals,
                    scopes,
                    unary_selector_spans,
                    out,
                );
            }
        }
        ExprKind::Paren(inner)
        | ExprKind::Return(inner)
        | ExprKind::Resend { message: inner } => {
            classify_identifier_usage(
                inner,
                top_level,
                globals,
                scopes,
                unary_selector_spans,
                out,
            );
        }
        ExprKind::DirectedResend { message, .. } => {
            classify_identifier_usage(
                message,
                top_level,
                globals,
                scopes,
                unary_selector_spans,
                out,
            );
        }
        ExprKind::Assignment { target, value, .. } => {
            classify_identifier_usage(
                target,
                top_level,
                globals,
                scopes,
                unary_selector_spans,
                out,
            );
            classify_identifier_usage(
                value,
                top_level,
                globals,
                scopes,
                unary_selector_spans,
                out,
            );
        }
        ExprKind::Block { args, body } => {
            let mut scope = Scope::default();
            for arg in args {
                scope.locals.insert(arg.clone());
            }
            for name in immediate_assignment_names(body) {
                scope.locals.insert(name);
            }
            scopes.push(scope);
            for e in body {
                classify_identifier_usage(
                    e,
                    false,
                    globals,
                    scopes,
                    unary_selector_spans,
                    out,
                );
            }
            scopes.pop();
        }
        ExprKind::Object { slots, body } => {
            for slot in slots {
                if slot.params.is_empty() {
                    classify_identifier_usage(
                        &slot.value,
                        false,
                        globals,
                        scopes,
                        unary_selector_spans,
                        out,
                    );
                } else {
                    let mut scope = Scope::default();
                    for param in &slot.params {
                        scope.locals.insert(param.clone());
                    }
                    scopes.push(scope);
                    classify_identifier_usage(
                        &slot.value,
                        false,
                        globals,
                        scopes,
                        unary_selector_spans,
                        out,
                    );
                    scopes.pop();
                }
            }

            let locals = immediate_assignment_names(body);
            if !locals.is_empty() {
                let mut scope = Scope::default();
                for name in locals {
                    scope.locals.insert(name);
                }
                scopes.push(scope);
                for e in body {
                    classify_identifier_usage(
                        e,
                        false,
                        globals,
                        scopes,
                        unary_selector_spans,
                        out,
                    );
                }
                scopes.pop();
            } else {
                for e in body {
                    classify_identifier_usage(
                        e,
                        false,
                        globals,
                        scopes,
                        unary_selector_spans,
                        out,
                    );
                }
            }
        }
        ExprKind::Sequence(exprs) => {
            for e in exprs {
                classify_identifier_usage(
                    e,
                    top_level,
                    globals,
                    scopes,
                    unary_selector_spans,
                    out,
                );
            }
        }
        ExprKind::Cascade { receiver, messages } => {
            classify_identifier_usage(
                receiver,
                top_level,
                globals,
                scopes,
                unary_selector_spans,
                out,
            );
            for msg in messages {
                classify_identifier_usage(
                    msg,
                    top_level,
                    globals,
                    scopes,
                    unary_selector_spans,
                    out,
                );
            }
        }
        _ => {}
    }
}

fn is_local(name: &str, scopes: &[Scope]) -> bool {
    scopes.iter().rev().any(|s| s.locals.contains(name))
}

fn immediate_assignment_names(exprs: &[Expr]) -> HashSet<String> {
    let mut names = HashSet::new();
    for expr in exprs {
        if let ExprKind::Assignment { target, .. } = &expr.kind {
            if let ExprKind::Ident(name) = &target.kind {
                names.insert(name.clone());
            }
        }
    }
    names
}

fn is_literal_ident(name: &str) -> bool {
    matches!(name, "True" | "False" | "None" | "true" | "false")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn emits_semantic_tokens_for_kette_categories() {
        let source = "Global := { foo = [ | x | x print ] }. Global foo: 1";
        let tokens = semantic_tokens(source);
        assert!(!tokens.is_empty());
    }
}
