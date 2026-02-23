use crate::ast::{
    AssignKind, AstArena, Comment, CommentKind, ExprId, ExprKind, ExprNode,
    KeywordPair, SlotDescriptor, SlotSelector,
};
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
    arena: AstArena,
    last_span: Span,
    at_eof: bool,
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
            arena: AstArena::default(),
            last_span: Span::point(Pos::origin()),
            at_eof: false,
            pending_comments: Vec::new(),
            op_precedence,
        }
    }

    pub fn arena(&self) -> &AstArena {
        &self.arena
    }

    pub fn into_arena(self) -> AstArena {
        self.arena
    }

    fn alloc_expr(&mut self, kind: ExprKind, span: Span) -> ExprId {
        self.arena.alloc(ExprNode {
            kind,
            span,
            leading_comments: Vec::new(),
        })
    }

    fn span_of(&self, id: ExprId) -> Span {
        self.arena.get(id).span
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
                    let tok = self.tokens.next().expect("peeked token exists");
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

    fn parse_expression_with_comments(&mut self) -> Result<ExprId, ParseError> {
        let comments = self.take_pending_comments();
        let expr = self.parse_expression()?;
        self.arena.get_mut(expr).leading_comments = comments;
        Ok(expr)
    }

    pub fn parse_expression(&mut self) -> Result<ExprId, ParseError> {
        self.parse_assignment_level()
    }

    fn parse_cascade_level(&mut self) -> Result<ExprId, ParseError> {
        let expr = self.parse_keyword_level()?;
        self.parse_cascade_tail(expr)
    }

    fn parse_cascade_tail(
        &mut self,
        expr: ExprId,
    ) -> Result<ExprId, ParseError> {
        if !matches!(self.peek_kind(), TokenKind::Semicolon) {
            return Ok(expr);
        }

        if !self.is_message_expr(expr) {
            return Err(ParseError::new(
                "expected cascade message",
                self.span_of(expr),
            ));
        }

        let receiver = self.cascade_receiver_from_expr(expr);
        let mut messages = vec![expr];

        while matches!(self.peek_kind(), TokenKind::Semicolon) {
            self.advance();
            let msg = self.parse_cascade_message(receiver)?;
            messages.push(msg);
        }

        let start = self.span_of(receiver);
        let end =
            self.span_of(*messages.last().expect("messages always non-empty"));
        Ok(self.alloc_expr(
            ExprKind::Cascade { receiver, messages },
            start.merge(end),
        ))
    }

    fn parse_message_chain_from(
        &mut self,
        primary: ExprId,
    ) -> Result<ExprId, ParseError> {
        let expr = self.parse_unary_tail(primary);
        let expr = self.parse_binary_with_left(expr, 0)?;
        let expr = if matches!(self.peek_kind(), TokenKind::Keyword(_)) {
            self.parse_keyword_tail(expr)?
        } else {
            expr
        };
        self.parse_cascade_tail(expr)
    }

    fn parse_assignment_level(&mut self) -> Result<ExprId, ParseError> {
        let left = self.parse_cascade_level()?;
        self.parse_assignment_tail(left)
    }

    fn cascade_receiver_from_expr(&mut self, expr_id: ExprId) -> ExprId {
        let span = self.span_of(expr_id);
        match &self.arena.get(expr_id).kind {
            ExprKind::UnaryMessage { receiver, .. } => *receiver,
            ExprKind::BinaryMessage { receiver, .. } => *receiver,
            ExprKind::KeywordMessage { receiver, .. } => *receiver,
            ExprKind::Resend { .. } | ExprKind::DirectedResend { .. } => {
                self.alloc_expr(ExprKind::SelfRef, span)
            }
            _ => expr_id,
        }
    }

    fn is_message_expr(&self, expr_id: ExprId) -> bool {
        matches!(
            self.arena.get(expr_id).kind,
            ExprKind::UnaryMessage { .. }
                | ExprKind::BinaryMessage { .. }
                | ExprKind::KeywordMessage { .. }
                | ExprKind::Resend { .. }
                | ExprKind::DirectedResend { .. }
        )
    }

    fn parse_cascade_message(
        &mut self,
        receiver: ExprId,
    ) -> Result<ExprId, ParseError> {
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

        let receiver = self.alloc_expr(ExprKind::SelfRef, delegate_span);
        let message = self.parse_cascade_message(receiver)?;
        if !self.is_message_expr(message) {
            return Err(ParseError::new(
                "expected resend message",
                self.span_of(message),
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

    fn parse_keyword_level(&mut self) -> Result<ExprId, ParseError> {
        let recv = self.parse_binary_level()?;
        if matches!(self.peek_kind(), TokenKind::Keyword(_)) {
            self.parse_keyword_tail(recv)
        } else {
            Ok(recv)
        }
    }

    fn parse_keyword_tail(
        &mut self,
        receiver: ExprId,
    ) -> Result<ExprId, ParseError> {
        let start = self.span_of(receiver);
        let mut pairs = Vec::new();

        while let TokenKind::Keyword(kw) = self.peek_kind().clone() {
            let kt = self.advance();
            let arg = self.parse_binary_level()?;
            pairs.push(KeywordPair {
                keyword: kw,
                keyword_span: kt.span,
                span: kt.span.merge(self.span_of(arg)),
                argument: arg,
            });
        }

        let end = pairs.last().map(|p| p.span).unwrap_or(start);
        Ok(self.alloc_expr(
            ExprKind::KeywordMessage { receiver, pairs },
            start.merge(end),
        ))
    }

    fn parse_binary_level(&mut self) -> Result<ExprId, ParseError> {
        self.parse_binary_with_min_precedence(0)
    }

    fn parse_binary_with_min_precedence(
        &mut self,
        min_prec: u8,
    ) -> Result<ExprId, ParseError> {
        let left = self.parse_unary_level()?;
        self.parse_binary_with_left(left, min_prec)
    }

    fn parse_binary_with_left(
        &mut self,
        mut left: ExprId,
        min_prec: u8,
    ) -> Result<ExprId, ParseError> {
        while let TokenKind::Operator(op) = self.peek_kind().clone() {
            let prec = self.operator_precedence(&op);
            if prec < min_prec {
                break;
            }
            self.advance();
            let right = self.parse_binary_with_min_precedence(prec + 1)?;
            let span = self.span_of(left).merge(self.span_of(right));
            left = self.alloc_expr(
                ExprKind::BinaryMessage {
                    receiver: left,
                    operator: op,
                    operator_span: self.last_span,
                    argument: right,
                },
                span,
            );
        }
        Ok(left)
    }

    fn operator_precedence(&self, op: &str) -> u8 {
        *self.op_precedence.get(op).unwrap_or(&1)
    }

    fn parse_unary_level(&mut self) -> Result<ExprId, ParseError> {
        let expr = self.parse_primary()?;
        Ok(self.parse_unary_tail(expr))
    }

    fn parse_unary_tail(&mut self, mut expr: ExprId) -> ExprId {
        while let TokenKind::Identifier(_) = self.peek_kind().clone() {
            let tok = self.advance();
            let sel = match tok.kind {
                TokenKind::Identifier(s) => s,
                _ => unreachable!(),
            };
            let span = self.span_of(expr).merge(tok.span);
            expr = self.alloc_expr(
                ExprKind::UnaryMessage {
                    receiver: expr,
                    selector: sel,
                    selector_span: tok.span,
                },
                span,
            );
        }
        expr
    }

    fn parse_primary(&mut self) -> Result<ExprId, ParseError> {
        match self.peek_kind().clone() {
            TokenKind::Integer(_) => {
                let t = self.advance();
                let v = match t.kind {
                    TokenKind::Integer(v) => v,
                    _ => unreachable!(),
                };
                Ok(self.alloc_expr(ExprKind::Integer(v), t.span))
            }
            TokenKind::Float(_) => {
                let t = self.advance();
                let v = match t.kind {
                    TokenKind::Float(v) => v,
                    _ => unreachable!(),
                };
                Ok(self.alloc_expr(ExprKind::Float(v), t.span))
            }
            TokenKind::String(_) => {
                let t = self.advance();
                let v = match t.kind {
                    TokenKind::String(v) => v,
                    _ => unreachable!(),
                };
                Ok(self.alloc_expr(ExprKind::String(v), t.span))
            }
            TokenKind::Symbol(_) => {
                let t = self.advance();
                let v = match t.kind {
                    TokenKind::Symbol(v) => v,
                    _ => unreachable!(),
                };
                Ok(self.alloc_expr(ExprKind::Symbol(v), t.span))
            }
            TokenKind::SelfKw => {
                let t = self.advance();
                Ok(self.alloc_expr(ExprKind::SelfRef, t.span))
            }
            TokenKind::Identifier(_) => {
                let t = self.advance();
                let n = match t.kind {
                    TokenKind::Identifier(s) => s,
                    _ => unreachable!(),
                };
                let (n, span) = self.parse_qualified_ident_tail(n, t.span)?;
                Ok(self.alloc_expr(ExprKind::Ident(n), span))
            }
            TokenKind::ResendKw => {
                let t = self.advance();
                let start = t.span;
                let msg = self.parse_resend_message()?;
                let span = start.merge(msg.span(self));
                match msg {
                    ResendMessage::Undirected(message) => {
                        Ok(self.alloc_expr(ExprKind::Resend { message }, span))
                    }
                    ResendMessage::Directed { delegate, message } => Ok(self
                        .alloc_expr(
                            ExprKind::DirectedResend { delegate, message },
                            span,
                        )),
                }
            }
            TokenKind::LParen => self.parse_paren(),
            TokenKind::LBracket => self.parse_block(),
            TokenKind::LBrace => self.parse_object_literal(),
            TokenKind::Caret => {
                let t = self.advance();
                let e = self.parse_expression()?;
                let span = t.span.merge(self.span_of(e));
                Ok(self.alloc_expr(ExprKind::Return(e), span))
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

    fn parse_qualified_ident_tail(
        &mut self,
        mut name: String,
        mut span: Span,
    ) -> Result<(String, Span), ParseError> {
        while matches!(self.peek_kind(), TokenKind::PathSep) {
            self.advance();
            let tok = self.advance();
            let segment = match tok.kind {
                TokenKind::Identifier(s) => s,
                _ => {
                    return Err(ParseError::new(
                        "expected identifier after `::`",
                        tok.span,
                    ));
                }
            };
            name.push_str("::");
            name.push_str(&segment);
            span = span.merge(tok.span);
        }
        Ok((name, span))
    }

    fn parse_paren(&mut self) -> Result<ExprId, ParseError> {
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
            Ok(self.alloc_expr(ExprKind::Sequence(exprs), span))
        } else {
            let close = self.expect(&TokenKind::RParen)?;
            Ok(self.alloc_expr(ExprKind::Paren(expr), start.merge(close.span)))
        }
    }

    fn parse_object_literal(&mut self) -> Result<ExprId, ParseError> {
        let open = self.advance();
        let start = open.span;

        let mut slots: Vec<SlotDescriptor> = Vec::new();
        let mut body: Vec<ExprId> = Vec::new();
        let mut used_shorthand = false;
        let mut saw_non_assignment_body_expr = false;

        loop {
            let _ = self.peek_kind();
            if self.check(&TokenKind::RBrace) || self.at_eof {
                for c in self.take_pending_comments() {
                    let span = c.span;
                    body.push(self.alloc_expr(ExprKind::Comment(c), span));
                }
                break;
            }

            let comments = self.take_pending_comments();

            match self.peek_kind().clone() {
                TokenKind::Identifier(_) => {
                    let ident_tok = self.advance();
                    let name = match ident_tok.kind {
                        TokenKind::Identifier(s) => s,
                        _ => unreachable!(),
                    };

                    if saw_non_assignment_body_expr {
                        let ident_expr = self
                            .alloc_expr(ExprKind::Ident(name), ident_tok.span);
                        self.arena.get_mut(ident_expr).leading_comments =
                            comments;
                        let expr = self.continue_expression_from(ident_expr)?;
                        if !matches!(
                            self.arena.get(expr).kind,
                            ExprKind::Assignment { .. }
                        ) {
                            saw_non_assignment_body_expr = true;
                        }
                        body.push(expr);
                    } else {
                        match self.peek_kind().clone() {
                            TokenKind::Equals => {
                                let t = self.advance();
                                let value = self.parse_expression()?;
                                let span = ident_tok
                                    .span
                                    .merge(t.span)
                                    .merge(self.span_of(value));
                                slots.push(SlotDescriptor {
                                    selector: SlotSelector::Unary(name),
                                    params: vec![],
                                    mutable: false,
                                    is_parent: false,
                                    shorthand: false,
                                    value,
                                    span,
                                    leading_comments: comments,
                                });
                            }
                            TokenKind::Assign => {
                                let t = self.advance();
                                let value = self.parse_expression()?;
                                let span = ident_tok
                                    .span
                                    .merge(t.span)
                                    .merge(self.span_of(value));
                                slots.push(SlotDescriptor {
                                    selector: SlotSelector::Unary(name),
                                    params: vec![],
                                    mutable: true,
                                    is_parent: false,
                                    shorthand: false,
                                    value,
                                    span,
                                    leading_comments: comments,
                                });
                            }
                            TokenKind::Operator(ref op) if op == "*" => {
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
                                let span = ident_tok
                                    .span
                                    .merge(op_span)
                                    .merge(self.span_of(value));
                                slots.push(SlotDescriptor {
                                    selector: SlotSelector::Unary(name),
                                    params: vec![],
                                    mutable,
                                    is_parent: true,
                                    shorthand: false,
                                    value,
                                    span,
                                    leading_comments: comments,
                                });
                            }
                            TokenKind::Dot | TokenKind::RBrace => {
                                let value = self.alloc_expr(
                                    ExprKind::Ident(name.clone()),
                                    ident_tok.span,
                                );
                                slots.push(SlotDescriptor {
                                    selector: SlotSelector::Unary(name),
                                    params: vec![],
                                    mutable: true,
                                    is_parent: false,
                                    shorthand: true,
                                    value,
                                    span: ident_tok.span,
                                    leading_comments: comments,
                                });
                                used_shorthand = true;
                            }
                            _ => {
                                let ident_expr = self.alloc_expr(
                                    ExprKind::Ident(name),
                                    ident_tok.span,
                                );
                                self.arena
                                    .get_mut(ident_expr)
                                    .leading_comments = comments;
                                let expr =
                                    self.continue_expression_from(ident_expr)?;
                                if !matches!(
                                    self.arena.get(expr).kind,
                                    ExprKind::Assignment { .. }
                                ) {
                                    if used_shorthand {
                                        return Err(ParseError::new(
                                            "shorthand slots are only allowed in pure data objects",
                                            self.span_of(expr),
                                        ));
                                    }
                                    saw_non_assignment_body_expr = true;
                                }
                                body.push(expr);
                            }
                        }
                    }
                }
                TokenKind::Keyword(_) | TokenKind::Operator(_) => {
                    if saw_non_assignment_body_expr {
                        let expr = self.parse_expression()?;
                        self.arena.get_mut(expr).leading_comments = comments;
                        if !matches!(
                            self.arena.get(expr).kind,
                            ExprKind::Assignment { .. }
                        ) {
                            saw_non_assignment_body_expr = true;
                        }
                        body.push(expr);
                    } else {
                        let mut sd = self.parse_slot_descriptor()?;
                        sd.leading_comments = comments;
                        slots.push(sd);
                    }
                }
                _ => {
                    let expr = self.parse_expression()?;
                    self.arena.get_mut(expr).leading_comments = comments;
                    if !matches!(
                        self.arena.get(expr).kind,
                        ExprKind::Assignment { .. }
                    ) {
                        if used_shorthand {
                            return Err(ParseError::new(
                                "shorthand slots are only allowed in pure data objects",
                                self.span_of(expr),
                            ));
                        }
                        saw_non_assignment_body_expr = true;
                    }
                    body.push(expr);
                }
            }

            if matches!(self.peek_kind(), TokenKind::Dot) {
                self.advance();
            } else {
                let _ = self.peek_kind();
                for c in self.take_pending_comments() {
                    let span = c.span;
                    body.push(self.alloc_expr(ExprKind::Comment(c), span));
                }
                break;
            }
        }

        let close = self.expect(&TokenKind::RBrace)?;
        Ok(self.alloc_expr(
            ExprKind::Object { slots, body },
            start.merge(close.span),
        ))
    }

    fn continue_expression_from(
        &mut self,
        primary: ExprId,
    ) -> Result<ExprId, ParseError> {
        let expr = self.parse_message_chain_from(primary)?;
        self.parse_assignment_tail(expr)
    }

    fn parse_assignment_tail(
        &mut self,
        left: ExprId,
    ) -> Result<ExprId, ParseError> {
        match self.peek_kind().clone() {
            TokenKind::Assign | TokenKind::Equals => {
                let op = self.advance();
                let right = self.parse_assignment_level()?;
                let kind = match op.kind {
                    TokenKind::Assign => AssignKind::Assign,
                    TokenKind::Equals => AssignKind::Const,
                    _ => unreachable!(),
                };
                let span = self.span_of(left).merge(self.span_of(right));
                Ok(self.alloc_expr(
                    ExprKind::Assignment {
                        target: left,
                        kind,
                        value: right,
                    },
                    span,
                ))
            }
            _ => Ok(left),
        }
    }

    fn parse_block(&mut self) -> Result<ExprId, ParseError> {
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
        Ok(self.alloc_expr(
            ExprKind::Block { args, body },
            start.merge(close.span),
        ))
    }

    fn parse_code_body(
        &mut self,
        terminator: &TokenKind,
    ) -> Result<Vec<ExprId>, ParseError> {
        let mut exprs = Vec::new();
        loop {
            let _ = self.peek_kind();
            if self.check(terminator) || self.at_eof {
                for c in self.take_pending_comments() {
                    let span = c.span;
                    exprs.push(self.alloc_expr(ExprKind::Comment(c), span));
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
                    exprs.push(self.alloc_expr(ExprKind::Comment(c), span));
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
                let span = start.merge(op_span).merge(self.span_of(value));
                Ok(SlotDescriptor {
                    selector: SlotSelector::Unary(name),
                    params: vec![],
                    mutable,
                    is_parent,
                    shorthand: false,
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
                let span = start.merge(op_span).merge(self.span_of(value));
                Ok(SlotDescriptor {
                    selector: SlotSelector::Keyword(selector),
                    params: arguments,
                    mutable,
                    is_parent: false,
                    shorthand: false,
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
                let span = start.merge(op_span).merge(self.span_of(value));
                Ok(SlotDescriptor {
                    selector: SlotSelector::Binary(op),
                    params: arguments,
                    mutable,
                    is_parent: false,
                    shorthand: false,
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
    Undirected(ExprId),
    Directed { delegate: String, message: ExprId },
}

impl ResendMessage {
    fn span<I: Iterator<Item = Token>>(&self, parser: &Parser<I>) -> Span {
        match self {
            ResendMessage::Undirected(expr_id) => parser.span_of(*expr_id),
            ResendMessage::Directed { message, .. } => parser.span_of(*message),
        }
    }
}

impl<I: Iterator<Item = Token>> Iterator for Parser<I> {
    type Item = Result<ExprId, ParseError>;

    fn next(&mut self) -> Option<Result<ExprId, ParseError>> {
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
                let id = self.alloc_expr(ExprKind::Comment(c), span);
                return Some(Ok(id));
            }
            self.at_eof = true;
            return None;
        }
        Some(self.parse_expression_with_comments())
    }
}
