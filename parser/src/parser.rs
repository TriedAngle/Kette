/// Streaming parser for Self expression syntax.
///
/// Consumes tokens and produces [`Expr`] AST nodes.
///
/// # Comment preservation
///
/// Comments are **never discarded**.  Before an expression they are
/// attached as [`Expr::leading_comments`].  At the end of a body they
/// are emitted as [`ExprKind::Comment`] nodes for LSP reflection.
use crate::ast::*;
use crate::span::{Pos, Span};
use crate::token::{Token, TokenKind};
use std::collections::HashMap;

#[derive(Debug, Clone, PartialEq)]
pub struct ParseError {
    pub message: String,
    pub span: Span,
}

impl ParseError {
    pub fn new(message: impl Into<String>, span: Span) -> Self {
        Self {
            message: message.into(),
            span,
        }
    }
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} at {}", self.message, self.span)
    }
}

impl std::error::Error for ParseError {}

pub struct Parser<I: Iterator<Item = Token>> {
    tokens: std::iter::Peekable<I>,
    last_span: Span,
    at_eof: bool,
    /// Comments buffered while scanning for the next meaningful token.
    pending_comments: Vec<Comment>,
    op_precedence: HashMap<String, u8>,
}

impl<I: Iterator<Item = Token>> Parser<I> {
    pub fn new(tokens: I) -> Self {
        let mut op_precedence = HashMap::new();
        op_precedence.insert("+".to_string(), 1);
        op_precedence.insert("-".to_string(), 1);
        op_precedence.insert("*".to_string(), 2);
        op_precedence.insert("/".to_string(), 2);
        Self {
            tokens: tokens.peekable(),
            last_span: Span::point(Pos::origin()),
            at_eof: false,
            pending_comments: Vec::new(),
            op_precedence,
        }
    }

    fn peek_kind(&mut self) -> &TokenKind {
        self.collect_comments();
        match self.tokens.peek() {
            Some(tok) => &tok.kind,
            None => &TokenKind::Eof,
        }
    }

    fn peek_span(&mut self) -> Span {
        self.collect_comments();
        match self.tokens.peek() {
            Some(tok) => tok.span,
            None => self.last_span,
        }
    }

    fn collect_comments(&mut self) {
        loop {
            match self.tokens.peek() {
                Some(tok) if tok.kind.is_comment() => {
                    let tok = self.tokens.next().unwrap();
                    self.last_span = tok.span;
                    self.pending_comments.push(token_to_comment(&tok));
                }
                _ => break,
            }
        }
    }

    fn take_pending_comments(&mut self) -> Vec<Comment> {
        std::mem::take(&mut self.pending_comments)
    }

    fn advance(&mut self) -> Token {
        self.collect_comments();
        match self.tokens.next() {
            Some(tok) => {
                self.last_span = tok.span;
                if matches!(tok.kind, TokenKind::Eof) {
                    self.at_eof = true;
                }
                tok
            }
            None => {
                self.at_eof = true;
                Token::new(TokenKind::Eof, self.last_span, "")
            }
        }
    }

    fn expect(&mut self, expected: &TokenKind) -> Result<Token, ParseError> {
        let tok = self.advance();
        if std::mem::discriminant(&tok.kind) == std::mem::discriminant(expected)
        {
            Ok(tok)
        } else {
            Err(ParseError::new(
                format!(
                    "expected {}, found {}",
                    expected.name(),
                    tok.kind.name()
                ),
                tok.span,
            ))
        }
    }

    fn check(&mut self, kind: &TokenKind) -> bool {
        std::mem::discriminant(self.peek_kind()) == std::mem::discriminant(kind)
    }

    fn parse_expression_with_comments(&mut self) -> Result<Expr, ParseError> {
        let comments = self.take_pending_comments();
        let expr = self.parse_expression()?;
        Ok(expr.with_comments(comments))
    }

    pub fn parse_expression(&mut self) -> Result<Expr, ParseError> {
        self.parse_cascade_level()
    }

    fn parse_cascade_level(&mut self) -> Result<Expr, ParseError> {
        let expr = self.parse_assignment_level()?;
        if !matches!(self.peek_kind(), TokenKind::Semicolon) {
            return Ok(expr);
        }

        if !self.is_message_expr(&expr) {
            return Err(ParseError::new("expected cascade message", expr.span));
        }

        let receiver = self.cascade_receiver_from_expr(&expr);
        let mut messages = vec![expr];

        while matches!(self.peek_kind(), TokenKind::Semicolon) {
            self.advance();
            let msg = self.parse_cascade_message(receiver.clone())?;
            messages.push(msg);
        }

        let start = receiver.span;
        let end = messages.last().map(|e| e.span).unwrap_or(start);
        Ok(Expr::new(
            ExprKind::Cascade {
                receiver: Box::new(receiver),
                messages,
            },
            start.merge(end),
        ))
    }

    fn parse_assignment_level(&mut self) -> Result<Expr, ParseError> {
        let left = self.parse_keyword_level()?;
        match self.peek_kind().clone() {
            TokenKind::Assign | TokenKind::Equals => {
                let op = self.advance();
                let right = self.parse_assignment_level()?;
                let kind = match op.kind {
                    TokenKind::Assign => AssignKind::Assign,
                    TokenKind::Equals => AssignKind::Const,
                    _ => unreachable!(),
                };
                let span = left.span.merge(right.span);
                Ok(Expr::new(
                    ExprKind::Assignment {
                        target: Box::new(left),
                        kind,
                        value: Box::new(right),
                    },
                    span,
                ))
            }
            _ => Ok(left),
        }
    }

    fn cascade_receiver_from_expr(&self, expr: &Expr) -> Expr {
        match &expr.kind {
            ExprKind::UnaryMessage { receiver, .. } => (**receiver).clone(),
            ExprKind::BinaryMessage { receiver, .. } => (**receiver).clone(),
            ExprKind::KeywordMessage { receiver, .. } => (**receiver).clone(),
            ExprKind::Resend { .. } | ExprKind::DirectedResend { .. } => {
                Expr::new(ExprKind::SelfRef, expr.span)
            }
            _ => expr.clone(),
        }
    }

    fn is_message_expr(&self, expr: &Expr) -> bool {
        matches!(
            expr.kind,
            ExprKind::UnaryMessage { .. }
                | ExprKind::BinaryMessage { .. }
                | ExprKind::KeywordMessage { .. }
                | ExprKind::Resend { .. }
                | ExprKind::DirectedResend { .. }
        )
    }

    fn parse_cascade_message(
        &mut self,
        receiver: Expr,
    ) -> Result<Expr, ParseError> {
        match self.peek_kind().clone() {
            TokenKind::Identifier(_) => {
                let expr = self.parse_unary_tail(receiver);
                let expr = self.parse_binary_with_left(expr, 0)?;
                if matches!(self.peek_kind(), TokenKind::Keyword(_)) {
                    self.parse_keyword_tail(expr)
                } else {
                    Ok(expr)
                }
            }
            TokenKind::Operator(_) => {
                let expr = self.parse_binary_with_left(receiver, 0)?;
                if matches!(self.peek_kind(), TokenKind::Keyword(_)) {
                    self.parse_keyword_tail(expr)
                } else {
                    Ok(expr)
                }
            }
            TokenKind::Keyword(_) => self.parse_keyword_tail(receiver),
            _ => Err(ParseError::new(
                "expected cascade message",
                self.peek_span(),
            )),
        }
    }

    fn parse_resend_message(&mut self) -> Result<ResendMessage, ParseError> {
        let delegate_span = self.peek_span();
        let delegate = match self.peek_kind().clone() {
            TokenKind::SelfKw => {
                self.advance();
                None
            }
            TokenKind::Identifier(_) => {
                let token = self.advance();
                match token.kind {
                    TokenKind::Identifier(name) => Some(name),
                    _ => unreachable!(),
                }
            }
            _ => {
                return Err(ParseError::new(
                    "expected `self` or parent name after resend",
                    delegate_span,
                ));
            }
        };

        let receiver = Expr::new(ExprKind::SelfRef, delegate_span);
        let message = self.parse_cascade_message(receiver)?;
        if !self.is_message_expr(&message) {
            return Err(ParseError::new(
                "expected resend message",
                message.span,
            ));
        }

        match delegate {
            Some(name) => Ok(ResendMessage::Directed {
                delegate: name,
                message,
            }),
            None => Ok(ResendMessage::Undirected(message)),
        }
    }

    fn parse_keyword_level(&mut self) -> Result<Expr, ParseError> {
        let recv = self.parse_binary_level()?;
        if matches!(self.peek_kind(), TokenKind::Keyword(_)) {
            self.parse_keyword_tail(recv)
        } else {
            Ok(recv)
        }
    }

    fn parse_keyword_tail(
        &mut self,
        receiver: Expr,
    ) -> Result<Expr, ParseError> {
        let start = receiver.span;
        let mut pairs = Vec::new();

        if let TokenKind::Keyword(kw) = self.peek_kind().clone() {
            let kt = self.advance();
            let arg = self.parse_binary_level()?;
            pairs.push(KeywordPair {
                keyword: kw,
                span: kt.span.merge(arg.span),
                argument: arg,
            });
        }
        while let TokenKind::Keyword(kw) = self.peek_kind().clone() {
            let kt = self.advance();
            let arg = self.parse_binary_level()?;
            pairs.push(KeywordPair {
                keyword: kw,
                span: kt.span.merge(arg.span),
                argument: arg,
            });
        }

        let end = pairs.last().map(|p| p.span).unwrap_or(start);
        Ok(Expr::new(
            ExprKind::KeywordMessage {
                receiver: Box::new(receiver),
                pairs,
            },
            start.merge(end),
        ))
    }

    fn parse_binary_level(&mut self) -> Result<Expr, ParseError> {
        self.parse_binary_with_min_precedence(0)
    }

    fn parse_binary_with_min_precedence(
        &mut self,
        min_prec: u8,
    ) -> Result<Expr, ParseError> {
        let left = self.parse_unary_level()?;
        self.parse_binary_with_left(left, min_prec)
    }

    fn parse_binary_with_left(
        &mut self,
        mut left: Expr,
        min_prec: u8,
    ) -> Result<Expr, ParseError> {
        loop {
            let (op, prec) = match self.peek_kind().clone() {
                TokenKind::Operator(op) => {
                    let prec = self.operator_precedence(&op);
                    (op, prec)
                }
                _ => break,
            };
            if prec < min_prec {
                break;
            }
            self.advance();
            let right = self.parse_binary_with_min_precedence(prec + 1)?;
            let span = left.span.merge(right.span);
            left = Expr::new(
                ExprKind::BinaryMessage {
                    receiver: Box::new(left),
                    operator: op,
                    argument: Box::new(right),
                },
                span,
            );
        }
        Ok(left)
    }

    fn operator_precedence(&self, op: &str) -> u8 {
        *self.op_precedence.get(op).unwrap_or(&1)
    }

    fn parse_unary_level(&mut self) -> Result<Expr, ParseError> {
        let expr = self.parse_primary()?;
        Ok(self.parse_unary_tail(expr))
    }

    fn parse_unary_tail(&mut self, mut expr: Expr) -> Expr {
        loop {
            if let TokenKind::Identifier(_) = self.peek_kind() {
                let tok = self.advance();
                let sel = match tok.kind {
                    TokenKind::Identifier(s) => s,
                    _ => unreachable!(),
                };
                let span = expr.span.merge(tok.span);
                expr = Expr::new(
                    ExprKind::UnaryMessage {
                        receiver: Box::new(expr),
                        selector: sel,
                    },
                    span,
                );
            } else {
                break;
            }
        }
        expr
    }

    fn parse_primary(&mut self) -> Result<Expr, ParseError> {
        match self.peek_kind().clone() {
            TokenKind::Integer(_) => {
                let t = self.advance();
                let v = match t.kind {
                    TokenKind::Integer(v) => v,
                    _ => unreachable!(),
                };
                Ok(Expr::new(ExprKind::Integer(v), t.span))
            }
            TokenKind::Float(_) => {
                let t = self.advance();
                let v = match t.kind {
                    TokenKind::Float(v) => v,
                    _ => unreachable!(),
                };
                Ok(Expr::new(ExprKind::Float(v), t.span))
            }
            TokenKind::String(_) => {
                let t = self.advance();
                let v = match t.kind {
                    TokenKind::String(v) => v,
                    _ => unreachable!(),
                };
                Ok(Expr::new(ExprKind::String(v), t.span))
            }
            TokenKind::SelfKw => {
                let t = self.advance();
                Ok(Expr::new(ExprKind::SelfRef, t.span))
            }
            TokenKind::Identifier(_) => {
                let t = self.advance();
                let n = match t.kind {
                    TokenKind::Identifier(s) => s,
                    _ => unreachable!(),
                };
                Ok(Expr::new(ExprKind::Ident(n), t.span))
            }
            TokenKind::ResendKw => {
                let t = self.advance();
                let start = t.span;
                let msg = self.parse_resend_message()?;
                let span = start.merge(msg.span());
                match msg {
                    ResendMessage::Undirected(message) => Ok(Expr::new(
                        ExprKind::Resend {
                            message: Box::new(message),
                        },
                        span,
                    )),
                    ResendMessage::Directed { delegate, message } => {
                        Ok(Expr::new(
                            ExprKind::DirectedResend {
                                delegate,
                                message: Box::new(message),
                            },
                            span,
                        ))
                    }
                }
            }
            TokenKind::LParen => self.parse_paren(),
            TokenKind::LBracket => self.parse_block(),
            TokenKind::LBrace => self.parse_object_literal(),
            TokenKind::Caret => {
                let t = self.advance();
                let e = self.parse_expression()?;
                let span = t.span.merge(e.span);
                Ok(Expr::new(ExprKind::Return(Box::new(e)), span))
            }
            TokenKind::Keyword(_) | TokenKind::Operator(_) => {
                let _ = self.advance();
                Err(ParseError::new(
                    "expected explicit receiver before message",
                    self.peek_span(),
                ))
            }
            TokenKind::Eof => Err(ParseError::new(
                "unexpected end of input",
                self.peek_span(),
            )),
            _ => {
                let t = self.advance();
                Err(ParseError::new(
                    format!("unexpected token: {}", t.kind.name()),
                    t.span,
                ))
            }
        }
    }

    fn parse_paren(&mut self) -> Result<Expr, ParseError> {
        let open = self.advance();
        let start = open.span;

        if matches!(self.peek_kind(), TokenKind::RParen) {
            let close = self.advance();
            return Err(ParseError::new(
                "empty parentheses are not allowed",
                start.merge(close.span),
            ));
        }

        let expr = self.parse_expression()?;
        if matches!(self.peek_kind(), TokenKind::Dot) {
            let mut exprs = vec![expr];
            while matches!(self.peek_kind(), TokenKind::Dot) {
                self.advance();
                if matches!(self.peek_kind(), TokenKind::RParen) {
                    break;
                }
                exprs.push(self.parse_expression_with_comments()?);
            }
            let close = self.expect(&TokenKind::RParen)?;
            let span = start.merge(close.span);
            Ok(Expr::new(ExprKind::Sequence(exprs), span))
        } else {
            let close = self.expect(&TokenKind::RParen)?;
            Ok(Expr::new(
                ExprKind::Paren(Box::new(expr)),
                start.merge(close.span),
            ))
        }
    }

    fn parse_object_literal(&mut self) -> Result<Expr, ParseError> {
        let open = self.advance();
        let start = open.span;

        // Parse body: interleaved slot definitions and bare expressions.
        // - `ident =`/`:=`/`*` at statement start → slot definition
        // - `keyword:`/`operator` at statement start → slot definition
        //   (these can't start an expression without a receiver)
        // - anything else → bare expression (goes to body)
        let mut slots = Vec::new();
        let mut body = Vec::new();

        loop {
            let _ = self.peek_kind(); // collect comments
            if self.check(&TokenKind::RBrace) || self.at_eof {
                for c in self.take_pending_comments() {
                    let span = c.span;
                    body.push(Expr::new(ExprKind::Comment(c), span));
                }
                break;
            }

            let comments = self.take_pending_comments();

            match self.peek_kind().clone() {
                TokenKind::Identifier(_) => {
                    // Could be a slot definition or the start of an expression.
                    // Consume the identifier and look at what follows.
                    let ident_tok = self.advance();
                    let name = match ident_tok.kind {
                        TokenKind::Identifier(s) => s,
                        _ => unreachable!(),
                    };

                    match self.peek_kind().clone() {
                        TokenKind::Equals => {
                            // Unary const slot: name = expr
                            let t = self.advance();
                            let value = self.parse_expression()?;
                            let span =
                                ident_tok.span.merge(t.span).merge(value.span);
                            slots.push(SlotDescriptor {
                                selector: SlotSelector::Unary(name),
                                params: vec![],
                                mutable: false,
                                is_parent: false,
                                value,
                                span,
                                leading_comments: comments,
                            });
                        }
                        TokenKind::Assign => {
                            // Unary mutable slot: name := expr
                            let t = self.advance();
                            let value = self.parse_expression()?;
                            let span =
                                ident_tok.span.merge(t.span).merge(value.span);
                            slots.push(SlotDescriptor {
                                selector: SlotSelector::Unary(name),
                                params: vec![],
                                mutable: true,
                                is_parent: false,
                                value,
                                span,
                                leading_comments: comments,
                            });
                        }
                        TokenKind::Operator(ref op) if op == "*" => {
                            // Parent slot: name* = expr
                            self.advance();
                            let (mutable, op_span) = match self
                                .peek_kind()
                                .clone()
                            {
                                TokenKind::Equals => {
                                    let t = self.advance();
                                    (false, t.span)
                                }
                                TokenKind::Assign => {
                                    let t = self.advance();
                                    (true, t.span)
                                }
                                _ => {
                                    return Err(ParseError::new(
                                            "expected `=` or `:=` after parent slot",
                                            self.peek_span(),
                                        ));
                                }
                            };
                            let value = self.parse_expression()?;
                            let span =
                                ident_tok.span.merge(op_span).merge(value.span);
                            slots.push(SlotDescriptor {
                                selector: SlotSelector::Unary(name),
                                params: vec![],
                                mutable,
                                is_parent: true,
                                value,
                                span,
                                leading_comments: comments,
                            });
                        }
                        _ => {
                            // Not a slot — parse as expression from the
                            // already-consumed identifier.
                            let ident_expr = Expr::new(
                                ExprKind::Ident(name),
                                ident_tok.span,
                            )
                            .with_comments(comments);
                            let expr =
                                self.continue_expression_from(ident_expr)?;
                            body.push(expr);
                        }
                    }
                }
                TokenKind::Keyword(_) | TokenKind::Operator(_) => {
                    // Keywords and operators at statement position are always
                    // slot definitions (they can't start an expression without
                    // a receiver).
                    let mut sd = self.parse_slot_descriptor()?;
                    sd.leading_comments = comments;
                    slots.push(sd);
                }
                _ => {
                    // Everything else is a bare expression.
                    let expr = self.parse_expression()?.with_comments(comments);
                    body.push(expr);
                }
            }

            // Consume statement separator
            if matches!(self.peek_kind(), TokenKind::Dot) {
                self.advance();
            } else {
                let _ = self.peek_kind();
                for c in self.take_pending_comments() {
                    let span = c.span;
                    body.push(Expr::new(ExprKind::Comment(c), span));
                }
                break;
            }
        }

        let close = self.expect(&TokenKind::RBrace)?;
        Ok(Expr::new(
            ExprKind::Object { slots, body },
            start.merge(close.span),
        ))
    }

    /// Continue parsing an expression given a pre-parsed primary token.
    /// Chains through: unary → binary → keyword → assignment → cascade.
    fn continue_expression_from(
        &mut self,
        primary: Expr,
    ) -> Result<Expr, ParseError> {
        let expr = self.parse_unary_tail(primary);
        let expr = self.parse_binary_with_left(expr, 0)?;
        let expr = if matches!(self.peek_kind(), TokenKind::Keyword(_)) {
            self.parse_keyword_tail(expr)?
        } else {
            expr
        };
        // Assignment level
        let expr = match self.peek_kind().clone() {
            TokenKind::Assign | TokenKind::Equals => {
                let op = self.advance();
                let right = self.parse_assignment_level()?;
                let kind = match op.kind {
                    TokenKind::Assign => AssignKind::Assign,
                    TokenKind::Equals => AssignKind::Const,
                    _ => unreachable!(),
                };
                let span = expr.span.merge(right.span);
                Expr::new(
                    ExprKind::Assignment {
                        target: Box::new(expr),
                        kind,
                        value: Box::new(right),
                    },
                    span,
                )
            }
            _ => expr,
        };
        // Cascade level
        if matches!(self.peek_kind(), TokenKind::Semicolon)
            && self.is_message_expr(&expr)
        {
            let receiver = self.cascade_receiver_from_expr(&expr);
            let mut messages = vec![expr];
            while matches!(self.peek_kind(), TokenKind::Semicolon) {
                self.advance();
                let msg = self.parse_cascade_message(receiver.clone())?;
                messages.push(msg);
            }
            let start = receiver.span;
            let end = messages.last().map(|e| e.span).unwrap_or(start);
            Ok(Expr::new(
                ExprKind::Cascade {
                    receiver: Box::new(receiver),
                    messages,
                },
                start.merge(end),
            ))
        } else {
            Ok(expr)
        }
    }

    fn parse_block(&mut self) -> Result<Expr, ParseError> {
        let open = self.advance();
        let start = open.span;
        let mut args = Vec::new();

        if matches!(self.peek_kind(), TokenKind::Pipe) {
            self.advance();
            while !matches!(self.peek_kind(), TokenKind::Pipe) {
                if self.at_eof {
                    return Err(ParseError::new(
                        "unexpected end of input in block arguments",
                        self.peek_span(),
                    ));
                }
                let tok = self.advance();
                match tok.kind {
                    TokenKind::Identifier(name) => args.push(name),
                    _ => {
                        return Err(ParseError::new(
                            "expected identifier in block arguments",
                            tok.span,
                        ));
                    }
                }
            }
            self.expect(&TokenKind::Pipe)?;
        }

        let body = self.parse_code_body(&TokenKind::RBracket)?;
        let close = self.expect(&TokenKind::RBracket)?;
        Ok(Expr::new(
            ExprKind::Block { args, body },
            start.merge(close.span),
        ))
    }

    fn parse_code_body(
        &mut self,
        terminator: &TokenKind,
    ) -> Result<Vec<Expr>, ParseError> {
        let mut exprs = Vec::new();
        loop {
            let _ = self.peek_kind(); // collect comments
            if self.check(terminator) || self.at_eof {
                for c in self.take_pending_comments() {
                    let span = c.span;
                    exprs.push(Expr::new(ExprKind::Comment(c), span));
                }
                break;
            }
            exprs.push(self.parse_expression_with_comments()?);
            if matches!(self.peek_kind(), TokenKind::Dot) {
                self.advance();
            } else {
                let _ = self.peek_kind();
                for c in self.take_pending_comments() {
                    let span = c.span;
                    exprs.push(Expr::new(ExprKind::Comment(c), span));
                }
                break;
            }
        }
        Ok(exprs)
    }

    fn parse_slot_descriptor(&mut self) -> Result<SlotDescriptor, ParseError> {
        let start = self.peek_span();
        match self.peek_kind().clone() {
            TokenKind::Identifier(_name) => {
                let nt = self.advance();
                let mut name = match nt.kind {
                    TokenKind::Identifier(s) => s,
                    _ => unreachable!(),
                };
                let is_parent = match self.peek_kind().clone() {
                    TokenKind::Operator(op) if op == "*" => {
                        self.advance();
                        true
                    }
                    _ => false,
                };
                if is_parent {
                    name = name.trim_end_matches('*').to_string();
                    if name.is_empty() {
                        return Err(ParseError::new(
                            "parent slot name cannot be empty",
                            nt.span,
                        ));
                    }
                }
                let (mutable, op_span) = match self.peek_kind().clone() {
                    TokenKind::Equals => {
                        let t = self.advance();
                        (false, t.span)
                    }
                    TokenKind::Assign => {
                        let t = self.advance();
                        (true, t.span)
                    }
                    _ => {
                        return Err(ParseError::new(
                            "expected `=` or `:=` after slot name",
                            self.peek_span(),
                        ));
                    }
                };
                let value = self.parse_expression()?;
                let span = start.merge(op_span).merge(value.span);
                Ok(SlotDescriptor {
                    selector: SlotSelector::Unary(name),
                    params: vec![],
                    mutable,
                    is_parent,
                    value,
                    span,
                    leading_comments: vec![],
                })
            }
            TokenKind::Keyword(kw) => {
                let mut selector = String::new();
                let mut arguments = Vec::new();
                let _kt = self.advance();
                selector.push_str(&kw);
                match self.peek_kind().clone() {
                    TokenKind::Identifier(a) => {
                        self.advance();
                        arguments.push(a);
                    }
                    _ => {
                        return Err(ParseError::new(
                            "expected identifier after keyword",
                            self.peek_span(),
                        ));
                    }
                }
                while let TokenKind::Keyword(ck) = self.peek_kind().clone() {
                    self.advance();
                    selector.push_str(&ck);
                    match self.peek_kind().clone() {
                        TokenKind::Identifier(a) => {
                            self.advance();
                            arguments.push(a);
                        }
                        _ => {
                            return Err(ParseError::new(
                                "expected identifier after keyword",
                                self.peek_span(),
                            ));
                        }
                    }
                }
                let (mutable, op_span) = match self.peek_kind().clone() {
                    TokenKind::Equals => {
                        let t = self.advance();
                        (false, t.span)
                    }
                    TokenKind::Assign => {
                        let t = self.advance();
                        (true, t.span)
                    }
                    _ => {
                        return Err(ParseError::new(
                            "expected `=` or `:=` after keyword slot",
                            self.peek_span(),
                        ));
                    }
                };
                let value = self.parse_expression()?;
                let span = start.merge(op_span).merge(value.span);
                Ok(SlotDescriptor {
                    selector: SlotSelector::Keyword(selector),
                    params: arguments,
                    mutable,
                    is_parent: false,
                    value,
                    span,
                    leading_comments: vec![],
                })
            }
            TokenKind::Operator(op) => {
                let _ot = self.advance();
                let mut arguments = Vec::new();
                if let TokenKind::Identifier(a) = self.peek_kind().clone() {
                    self.advance();
                    arguments.push(a);
                }
                let (mutable, op_span) = match self.peek_kind().clone() {
                    TokenKind::Equals => {
                        let t = self.advance();
                        (false, t.span)
                    }
                    TokenKind::Assign => {
                        let t = self.advance();
                        (true, t.span)
                    }
                    _ => {
                        return Err(ParseError::new(
                            "expected `=` or `:=` after operator slot",
                            self.peek_span(),
                        ));
                    }
                };
                let value = self.parse_expression()?;
                let span = start.merge(op_span).merge(value.span);
                Ok(SlotDescriptor {
                    selector: SlotSelector::Binary(op),
                    params: arguments,
                    mutable,
                    is_parent: false,
                    value,
                    span,
                    leading_comments: vec![],
                })
            }
            other => Err(ParseError::new(
                format!("unexpected token in slot list: {}", other.name()),
                self.peek_span(),
            )),
        }
    }
}

fn token_to_comment(tok: &Token) -> Comment {
    match &tok.kind {
        TokenKind::LineComment(t) => Comment {
            kind: CommentKind::Line,
            text: t.clone(),
            span: tok.span,
        },
        TokenKind::BlockComment(t) => Comment {
            kind: CommentKind::Block,
            text: t.clone(),
            span: tok.span,
        },
        _ => unreachable!(),
    }
}

enum ResendMessage {
    Undirected(Expr),
    Directed { delegate: String, message: Expr },
}

impl ResendMessage {
    fn span(&self) -> Span {
        match self {
            ResendMessage::Undirected(expr) => expr.span,
            ResendMessage::Directed { message, .. } => message.span,
        }
    }
}

impl<I: Iterator<Item = Token>> Iterator for Parser<I> {
    type Item = Result<Expr, ParseError>;

    fn next(&mut self) -> Option<Result<Expr, ParseError>> {
        if self.at_eof {
            return None;
        }
        while matches!(self.peek_kind(), TokenKind::Dot) {
            self.advance();
        }
        let _ = self.peek_kind();
        if matches!(self.peek_kind(), TokenKind::Eof) {
            if !self.pending_comments.is_empty() {
                let c = self.pending_comments.remove(0);
                let span = c.span;
                return Some(Ok(Expr::new(ExprKind::Comment(c), span)));
            }
            self.at_eof = true;
            return None;
        }
        Some(self.parse_expression_with_comments())
    }
}
