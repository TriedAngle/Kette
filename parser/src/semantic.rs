use std::collections::{BTreeMap, HashMap, HashSet};

use crate::ast::{AssignKind, Expr, ExprKind, SlotDescriptor, SlotSelector};
use crate::span::Span;
use crate::token::{Token, TokenKind};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AnalysisMode {
    BestEffort,
    Strict,
}

#[derive(Debug, Clone)]
pub struct SemanticIssue {
    pub message: String,
    pub span: Span,
}

#[derive(Debug, Clone, Default)]
pub struct SemanticAnalysis {
    pub spans: Vec<SemanticSpan>,
    pub issues: Vec<SemanticIssue>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SemanticKind {
    UnaryMethod,
    KeywordMessage,
    Local,
    Global,
    Operator,
    Punctuation,
    LiteralNumber,
    LiteralString,
    Keyword,
    Comment,
    Parameter,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SemanticSpan {
    pub start: usize,
    pub end: usize,
    pub kind: SemanticKind,
}

#[derive(Default)]
struct Classified {
    by_span: BTreeMap<(usize, usize), SemanticKind>,
}

impl Classified {
    fn add(&mut self, start: usize, end: usize, kind: SemanticKind) {
        if end <= start {
            return;
        }
        self.by_span.entry((start, end)).or_insert(kind);
    }

    fn into_spans(self) -> Vec<SemanticSpan> {
        self.by_span
            .into_iter()
            .map(|((start, end), kind)| SemanticSpan { start, end, kind })
            .collect()
    }
}

#[derive(Default)]
struct Scope {
    params: HashSet<String>,
    locals: HashSet<String>,
}

pub fn analyze_semantics(
    tokens: &[Token],
    exprs: &[Expr],
) -> Vec<SemanticSpan> {
    analyze_semantics_with_mode(tokens, exprs, AnalysisMode::BestEffort).spans
}

pub fn analyze_semantics_with_mode(
    tokens: &[Token],
    exprs: &[Expr],
    mode: AnalysisMode,
) -> SemanticAnalysis {
    let mut classified = Classified::default();

    classify_keyword_operator_and_literal_tokens(tokens, &mut classified);

    for expr in exprs {
        classify_slot_param_declarations(expr, tokens, &mut classified);
    }

    let mut scopes = Vec::new();
    for expr in exprs {
        classify_identifier_usage(expr, &mut scopes, &mut classified);
    }

    let mut issues = Vec::new();
    if mode == AnalysisMode::Strict {
        let mut scopes = Vec::new();
        for expr in exprs {
            collect_strict_issues(expr, &mut scopes, &mut issues);
        }
    }

    SemanticAnalysis {
        spans: classified.into_spans(),
        issues,
    }
}

pub fn slot_selector_name(slot: &SlotDescriptor) -> String {
    match &slot.selector {
        SlotSelector::Unary(s) => s.clone(),
        SlotSelector::Binary(s) => s.clone(),
        SlotSelector::Keyword(s) => s.clone(),
    }
}

pub fn collect_assignment_names(exprs: &[Expr]) -> HashSet<String> {
    let mut names = HashSet::new();
    collect_assignment_names_into(exprs, &mut names);
    names
}

fn classify_keyword_operator_and_literal_tokens(
    tokens: &[Token],
    out: &mut Classified,
) {
    for tok in tokens {
        match &tok.kind {
            TokenKind::Keyword(_) => {
                out.add(
                    tok.span.start.offset,
                    tok.span.end.offset,
                    SemanticKind::KeywordMessage,
                );
            }
            TokenKind::Operator(_) | TokenKind::Assign | TokenKind::Equals => {
                out.add(
                    tok.span.start.offset,
                    tok.span.end.offset,
                    SemanticKind::Operator,
                );
            }
            TokenKind::LParen
            | TokenKind::RParen
            | TokenKind::LBracket
            | TokenKind::RBracket
            | TokenKind::LBrace
            | TokenKind::RBrace
            | TokenKind::Pipe
            | TokenKind::Dot
            | TokenKind::PathSep
            | TokenKind::Semicolon
            | TokenKind::Caret => {
                out.add(
                    tok.span.start.offset,
                    tok.span.end.offset,
                    SemanticKind::Punctuation,
                );
            }
            TokenKind::SelfKw => {
                out.add(
                    tok.span.start.offset,
                    tok.span.end.offset,
                    SemanticKind::Keyword,
                );
            }
            TokenKind::LineComment(_) | TokenKind::BlockComment(_) => {
                out.add(
                    tok.span.start.offset,
                    tok.span.end.offset,
                    SemanticKind::Comment,
                );
            }
            TokenKind::Identifier(name) if is_literal_ident(name) => {
                out.add(
                    tok.span.start.offset,
                    tok.span.end.offset,
                    SemanticKind::LiteralNumber,
                );
            }
            TokenKind::Integer(_) | TokenKind::Float(_) => {
                out.add(
                    tok.span.start.offset,
                    tok.span.end.offset,
                    SemanticKind::LiteralNumber,
                );
            }
            TokenKind::String(_) => {
                out.add(
                    tok.span.start.offset,
                    tok.span.end.offset,
                    SemanticKind::LiteralString,
                );
            }
            TokenKind::Symbol(_) => {
                out.add(
                    tok.span.start.offset,
                    tok.span.end.offset,
                    SemanticKind::Global,
                );
            }
            _ => {}
        }
    }
}

fn classify_identifier_usage(
    expr: &Expr,
    scopes: &mut Vec<Scope>,
    out: &mut Classified,
) {
    match &expr.kind {
        ExprKind::SelfRef => {
            out.add(
                expr.span.start.offset,
                expr.span.end.offset,
                SemanticKind::Keyword,
            );
        }
        ExprKind::Ident(name) => {
            let span = (expr.span.start.offset, expr.span.end.offset);
            if is_literal_ident(name) {
                out.add(span.0, span.1, SemanticKind::LiteralNumber);
                return;
            }
            let kind = if is_param(name, scopes) {
                SemanticKind::Parameter
            } else if is_local(name, scopes) {
                SemanticKind::Local
            } else {
                SemanticKind::Global
            };
            out.add(span.0, span.1, kind);
        }
        ExprKind::UnaryMessage {
            receiver,
            selector_span,
            ..
        } => {
            out.add(
                selector_span.start.offset,
                selector_span.end.offset,
                SemanticKind::UnaryMethod,
            );
            classify_identifier_usage(receiver, scopes, out);
        }
        ExprKind::Block { args, body } => {
            let mut scope = Scope::default();
            for arg in args {
                scope.params.insert(arg.clone());
            }
            for name in collect_assignment_names(body) {
                scope.locals.insert(name);
            }
            with_scope(scopes, scope, |scopes| {
                for e in body {
                    classify_identifier_usage(e, scopes, out);
                }
            });
        }
        ExprKind::Object { slots, body } => {
            let mut object_scope = Scope::default();
            for slot in slots {
                if let Some(name) = slot_local_name(slot) {
                    object_scope.locals.insert(name);
                }
            }
            with_scope(scopes, object_scope, |scopes| {
                for slot in slots {
                    let mut scope = Scope::default();
                    for param in &slot.params {
                        scope.params.insert(param.clone());
                    }
                    for name in immediate_assignment_names_in_expr(&slot.value)
                    {
                        scope.locals.insert(name);
                    }
                    with_scope(scopes, scope, |scopes| {
                        classify_identifier_usage(&slot.value, scopes, out);
                    });
                }

                let locals = collect_assignment_names(body);
                if !locals.is_empty() {
                    let mut scope = Scope::default();
                    for name in locals {
                        scope.locals.insert(name);
                    }
                    with_scope(scopes, scope, |scopes| {
                        for e in body {
                            classify_identifier_usage(e, scopes, out);
                        }
                    });
                } else {
                    for e in body {
                        classify_identifier_usage(e, scopes, out);
                    }
                }
            });
        }
        _ => for_each_direct_child(expr, |child| {
            classify_identifier_usage(child, scopes, out)
        }),
    }
}

fn classify_slot_param_declarations(
    expr: &Expr,
    tokens: &[Token],
    out: &mut Classified,
) {
    if let ExprKind::Object { slots, .. } = &expr.kind {
        for slot in slots {
            classify_slot_params_for_slot(slot, tokens, out);
        }
    }

    for_each_direct_child(expr, |child| {
        classify_slot_param_declarations(child, tokens, out)
    });
}

fn classify_slot_params_for_slot(
    slot: &SlotDescriptor,
    tokens: &[Token],
    out: &mut Classified,
) {
    if slot.params.is_empty() {
        return;
    }

    let header_start = slot.span.start.offset;
    let header_end = slot.value.span.start.offset;
    if header_end <= header_start {
        return;
    }

    let start_idx =
        tokens.partition_point(|tok| tok.span.end.offset <= header_start);
    let end_idx =
        tokens.partition_point(|tok| tok.span.start.offset < header_end);

    let mut remaining: HashSet<&str> =
        slot.params.iter().map(String::as_str).collect();
    for tok in &tokens[start_idx..end_idx] {
        if let TokenKind::Identifier(name) = &tok.kind {
            if remaining.contains(name.as_str()) {
                out.add(
                    tok.span.start.offset,
                    tok.span.end.offset,
                    SemanticKind::Parameter,
                );
                remaining.remove(name.as_str());
                if remaining.is_empty() {
                    break;
                }
            }
        }
    }
}

fn is_local(name: &str, scopes: &[Scope]) -> bool {
    scopes.iter().rev().any(|s| s.locals.contains(name))
}

fn is_param(name: &str, scopes: &[Scope]) -> bool {
    scopes.iter().rev().any(|s| s.params.contains(name))
}

fn immediate_assignment_names_in_expr(expr: &Expr) -> HashSet<String> {
    match &expr.kind {
        ExprKind::Object { body, .. }
        | ExprKind::Block { body, .. }
        | ExprKind::Sequence(body) => collect_assignment_names(body),
        _ => HashSet::new(),
    }
}

fn collect_assignment_names_into(exprs: &[Expr], out: &mut HashSet<String>) {
    for expr in exprs {
        match &expr.kind {
            ExprKind::Assignment { target, .. } => {
                if let ExprKind::Ident(name) = &target.kind {
                    out.insert(name.clone());
                }
            }
            ExprKind::Sequence(nested) => {
                collect_assignment_names_into(nested, out);
            }
            ExprKind::Paren(inner) => {
                collect_assignment_names_into(
                    std::slice::from_ref(inner.as_ref()),
                    out,
                );
            }
            _ => {}
        }
    }
}

fn slot_local_name(slot: &SlotDescriptor) -> Option<String> {
    match &slot.selector {
        SlotSelector::Unary(name) => Some(name.clone()),
        SlotSelector::Binary(_) | SlotSelector::Keyword(_) => None,
    }
}

fn is_literal_ident(name: &str) -> bool {
    matches!(name, "True" | "False" | "None" | "true" | "false")
}

#[derive(Clone, Copy)]
struct BindingInfo {
    mutable: bool,
}

#[derive(Default)]
struct StrictScope {
    bindings: HashMap<String, BindingInfo>,
}

fn collect_strict_issues(
    expr: &Expr,
    scopes: &mut Vec<StrictScope>,
    out: &mut Vec<SemanticIssue>,
) {
    match &expr.kind {
        ExprKind::Error(msg) => out.push(SemanticIssue {
            message: msg.clone(),
            span: expr.span,
        }),
        ExprKind::Assignment {
            target,
            kind,
            value,
        } => {
            match &target.kind {
                ExprKind::Ident(name) => {
                    if *kind == AssignKind::Assign {
                        if let Some(info) = lookup_binding(name, scopes) {
                            if !info.mutable {
                                out.push(SemanticIssue {
                                    message: "cannot assign to constant"
                                        .to_string(),
                                    span: target.span,
                                });
                            }
                        }
                    }
                }
                _ => out.push(SemanticIssue {
                    message: "assignment target must be an identifier"
                        .to_string(),
                    span: target.span,
                }),
            }
            collect_strict_issues(value, scopes, out);
        }
        ExprKind::Block { args, body } => {
            let mut scope = StrictScope::default();
            for arg in args {
                scope
                    .bindings
                    .insert(arg.clone(), BindingInfo { mutable: false });
            }
            for (name, mutable) in
                collect_assignment_decls_with_mutability(body)
            {
                scope.bindings.insert(name, BindingInfo { mutable });
            }
            with_scope(scopes, scope, |scopes| {
                for e in body {
                    collect_strict_issues(e, scopes, out);
                }
            });
        }
        ExprKind::Object { slots, body } => {
            let mut scope = StrictScope::default();
            for slot in slots {
                scope.bindings.insert(
                    slot_selector_name(slot),
                    BindingInfo {
                        mutable: slot.mutable,
                    },
                );
            }
            with_scope(scopes, scope, |scopes| {
                for slot in slots {
                    let mut slot_scope = StrictScope::default();
                    for param in &slot.params {
                        slot_scope.bindings.insert(
                            param.clone(),
                            BindingInfo { mutable: false },
                        );
                    }
                    for (name, mutable) in
                        collect_assignment_decls_in_expr(&slot.value)
                    {
                        slot_scope
                            .bindings
                            .insert(name, BindingInfo { mutable });
                    }
                    with_scope(scopes, slot_scope, |scopes| {
                        collect_strict_issues(&slot.value, scopes, out);
                    });
                }

                if !body.is_empty() {
                    let mut body_scope = StrictScope::default();
                    for (name, mutable) in
                        collect_assignment_decls_with_mutability(body)
                    {
                        body_scope
                            .bindings
                            .insert(name, BindingInfo { mutable });
                    }
                    with_scope(scopes, body_scope, |scopes| {
                        for e in body {
                            collect_strict_issues(e, scopes, out);
                        }
                    });
                }
            });
        }
        _ => for_each_direct_child(expr, |child| {
            collect_strict_issues(child, scopes, out)
        }),
    }
}

fn with_scope<T, R>(
    scopes: &mut Vec<T>,
    scope: T,
    f: impl FnOnce(&mut Vec<T>) -> R,
) -> R {
    scopes.push(scope);
    let result = f(scopes);
    scopes.pop();
    result
}

fn for_each_direct_child(expr: &Expr, mut f: impl FnMut(&Expr)) {
    match &expr.kind {
        ExprKind::UnaryMessage { receiver, .. } => f(receiver),
        ExprKind::BinaryMessage {
            receiver, argument, ..
        } => {
            f(receiver);
            f(argument);
        }
        ExprKind::KeywordMessage { receiver, pairs } => {
            f(receiver);
            for pair in pairs {
                f(&pair.argument);
            }
        }
        ExprKind::Paren(inner)
        | ExprKind::Return(inner)
        | ExprKind::Resend { message: inner } => f(inner),
        ExprKind::DirectedResend { message, .. } => f(message),
        ExprKind::Assignment { target, value, .. } => {
            f(target);
            f(value);
        }
        ExprKind::Block { body, .. } | ExprKind::Sequence(body) => {
            for e in body {
                f(e);
            }
        }
        ExprKind::Object { slots, body } => {
            for slot in slots {
                f(&slot.value);
            }
            for e in body {
                f(e);
            }
        }
        ExprKind::Cascade { receiver, messages } => {
            f(receiver);
            for msg in messages {
                f(msg);
            }
        }
        _ => {}
    }
}

fn collect_assignment_decls_with_mutability(
    exprs: &[Expr],
) -> HashMap<String, bool> {
    let mut decls = HashMap::new();
    collect_assignment_decls_into(exprs, &mut decls);
    decls
}

fn collect_assignment_decls_in_expr(expr: &Expr) -> HashMap<String, bool> {
    match &expr.kind {
        ExprKind::Object { body, .. }
        | ExprKind::Block { body, .. }
        | ExprKind::Sequence(body) => {
            collect_assignment_decls_with_mutability(body)
        }
        _ => HashMap::new(),
    }
}

fn collect_assignment_decls_into(
    exprs: &[Expr],
    out: &mut HashMap<String, bool>,
) {
    for expr in exprs {
        match &expr.kind {
            ExprKind::Assignment { target, kind, .. } => {
                if let ExprKind::Ident(name) = &target.kind {
                    out.entry(name.clone())
                        .or_insert(*kind == AssignKind::Assign);
                }
            }
            ExprKind::Sequence(nested) => {
                collect_assignment_decls_into(nested, out);
            }
            ExprKind::Paren(inner) => {
                collect_assignment_decls_into(
                    std::slice::from_ref(inner.as_ref()),
                    out,
                );
            }
            _ => {}
        }
    }
}

fn lookup_binding(name: &str, scopes: &[StrictScope]) -> Option<BindingInfo> {
    scopes
        .iter()
        .rev()
        .find_map(|scope| scope.bindings.get(name).copied())
}

#[cfg(test)]
mod tests {
    use crate::{Lexer, Parser};

    use super::*;

    fn parse_source(src: &str) -> (Vec<Token>, Vec<Expr>) {
        let tokens: Vec<Token> = Lexer::from_str(src)
            .filter(|t| !t.is_eof() && !matches!(t.kind, TokenKind::Error(_)))
            .collect();
        let exprs: Vec<Expr> = Parser::new(Lexer::from_str(src))
            .filter_map(Result::ok)
            .collect();
        (tokens, exprs)
    }

    #[test]
    fn semantic_marks_assignment_and_local() {
        let (tokens, exprs) = parse_source("[ x := 1. x ]");
        let spans = analyze_semantics(&tokens, &exprs);
        assert!(spans.iter().any(|s| s.kind == SemanticKind::Operator));
        assert!(spans.iter().any(|s| s.kind == SemanticKind::Local));
    }

    #[test]
    fn semantic_marks_slot_params() {
        let (tokens, exprs) =
            parse_source("{ + rhs = { rhs }. foo: a Bar: b = { a + b } }");
        let spans = analyze_semantics(&tokens, &exprs);
        let count = spans
            .iter()
            .filter(|s| s.kind == SemanticKind::Parameter)
            .count();
        assert!(count >= 4);
    }

    #[test]
    fn semantic_marks_strings_numbers_and_delimiters() {
        let (tokens, exprs) = parse_source("[ | x | { x := 42. \"ok\" } ]");
        let spans = analyze_semantics(&tokens, &exprs);
        assert!(spans.iter().any(|s| s.kind == SemanticKind::LiteralNumber));
        assert!(spans.iter().any(|s| s.kind == SemanticKind::LiteralString));
        assert!(spans.iter().any(|s| s.kind == SemanticKind::Operator));
    }

    #[test]
    fn strict_collects_multiple_issues() {
        let (tokens, exprs) = parse_source("[ x = 1. x := 2. y := 3 ]");
        let analysis =
            analyze_semantics_with_mode(&tokens, &exprs, AnalysisMode::Strict);
        assert!(!analysis.issues.is_empty());
    }
}
