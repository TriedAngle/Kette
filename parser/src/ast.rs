/// Abstract syntax tree nodes for expressions.
///
/// The parser produces a stream of [`Expr`] nodes. Each node carries a
/// [`Span`] so that downstream consumers (error reporting, IDE tooling,
/// source-maps) always know the exact source location.
///
/// # Comments as first-class nodes
///
/// Comments are **preserved** in the AST for downstream reflection
/// (LSP hover, documentation extraction, etc.). They appear in two
/// places:
///
/// 1. [`Expr::leading_comments`] — comments that appeared immediately
///    before an expression (attached to the next meaningful node).
/// 2. [`ExprKind::Comment`] — a free-standing comment that doesn't
///    attach to any expression (e.g. at the end of a code body).
///
/// # Precedence encoding
///
/// Distinct node variants for each message tier:
/// - [`ExprKind::UnaryMessage`]   — highest precedence
/// - [`ExprKind::BinaryMessage`]  — medium precedence (have precedence within their group too)
/// - [`ExprKind::KeywordMessage`] — lowest precedence
use crate::span::Span;

/// A single comment preserved from the source.
#[derive(Debug, Clone, PartialEq)]
pub struct Comment {
    /// The kind of comment.
    pub kind: CommentKind,
    /// The text content (without delimiters).
    pub text: String,
    /// Where it appeared in the source.
    pub span: Span,
}

/// Whether a comment was a line comment or a block comment.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CommentKind {
    /// `// ...`
    Line,
    /// `/* ... */`
    Block,
}

/// A top-level expression node.
#[derive(Debug, Clone, PartialEq)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
    /// Comments that appeared immediately before this expression.
    /// Useful for doc-comment extraction and LSP hover.
    pub leading_comments: Vec<Comment>,
}

impl Expr {
    pub fn new(kind: ExprKind, span: Span) -> Self {
        Self {
            kind,
            span,
            leading_comments: Vec::new(),
        }
    }

    pub fn with_comments(mut self, comments: Vec<Comment>) -> Self {
        self.leading_comments = comments;
        self
    }
}

/// The different forms a Self expression can take.
#[derive(Debug, Clone, PartialEq)]
pub enum ExprKind {
    /// Integer literal.
    Integer(i128),
    /// Floating-point literal.
    Float(f64),
    /// String literal.
    String(String),
    /// Symbol literal.
    Symbol(String),

    /// `self` keyword.
    SelfRef,
    /// A lexical identifier.
    Ident(String),

    /// A unary message send: `receiver selector`.
    ///
    /// Precedence: highest.  Associativity: left-to-right.
    UnaryMessage {
        receiver: Box<Expr>,
        selector: String,
        selector_span: Span,
    },

    /// A binary message send: `receiver op argument`.
    ///
    /// Precedence: table-driven.  Associativity: left-to-right for same op.
    BinaryMessage {
        receiver: Box<Expr>,
        operator: String,
        operator_span: Span,
        argument: Box<Expr>,
    },

    /// A keyword message send: `receiver key1: arg1 Key2: arg2 ...`.
    ///
    /// Precedence: lowest.  Associativity: right-to-left.
    KeywordMessage {
        receiver: Box<Expr>,
        /// Each pair is (keyword, argument-expression).
        pairs: Vec<KeywordPair>,
    },

    /// Undirected resend: `resend.selector ...`
    Resend { message: Box<Expr> },

    /// Directed resend: `parentName.selector ...`
    DirectedResend {
        delegate: String,
        message: Box<Expr>,
    },

    /// A parenthesized expression: `( expr )`.
    Paren(Box<Expr>),

    /// A block literal: `[ | args | code ]`.
    Block { args: Vec<String>, body: Vec<Expr> },

    /// An object literal: `{ slots. code. }`.
    ///
    /// Unifies objects and method bodies into a single construct.
    /// - `slots` are named bindings: `name = value`, `keyword: arg = value`, etc.
    /// - `body` contains bare expressions (code to execute; last is return value)
    ///
    /// Method parameters come from the enclosing [`SlotDescriptor`], not from
    /// the object itself.
    Object {
        slots: Vec<SlotDescriptor>,
        body: Vec<Expr>,
    },

    /// Return expression: `^ expr`.
    Return(Box<Expr>),

    /// Assignment expression: `target := expr` or `target = expr`.
    Assignment {
        target: Box<Expr>,
        kind: AssignKind,
        value: Box<Expr>,
    },

    /// A sequence of expressions separated by `.`.
    Sequence(Vec<Expr>),

    /// A cascade send: `receiver msg1; msg2; ...`.
    Cascade {
        receiver: Box<Expr>,
        messages: Vec<Expr>,
    },

    /// A free-standing comment that doesn't attach to an expression.
    /// This allows the full source to be reconstructed / reflected.
    Comment(Comment),

    /// A parse error — included in the AST so the stream is never
    /// interrupted; downstream can decide whether to bail out.
    Error(String),
}

/// A single keyword-argument pair within a keyword message.
#[derive(Debug, Clone, PartialEq)]
pub struct KeywordPair {
    pub keyword: String,
    pub keyword_span: Span,
    pub argument: Expr,
    pub span: Span,
}

/// The assignment operator kind.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AssignKind {
    /// `:=` (assign to read-write slot).
    Assign,
    /// `=` (initialize read-only slot).
    Const,
}

pub fn to_dot(exprs: &[Expr]) -> String {
    let mut builder = DotBuilder::new();
    let root = builder.add_node("Program");
    for (idx, expr) in exprs.iter().enumerate() {
        let child = builder.walk_expr(expr);
        builder.add_edge(root, child, Some(&format!("expr[{}]", idx)));
    }
    builder.finish()
}

struct DotBuilder {
    next_id: usize,
    nodes: Vec<String>,
    edges: Vec<String>,
}

impl DotBuilder {
    fn new() -> Self {
        Self {
            next_id: 0,
            nodes: Vec::new(),
            edges: Vec::new(),
        }
    }

    fn finish(mut self) -> String {
        let mut out = String::new();
        out.push_str("digraph AST {\n");
        out.push_str("  node [shape=box];\n");
        for node in self.nodes.drain(..) {
            out.push_str("  ");
            out.push_str(&node);
            out.push('\n');
        }
        for edge in self.edges.drain(..) {
            out.push_str("  ");
            out.push_str(&edge);
            out.push('\n');
        }
        out.push_str("}\n");
        out
    }

    fn add_node(&mut self, label: &str) -> usize {
        let id = self.next_id;
        self.next_id += 1;
        let label = escape_label(label);
        self.nodes.push(format!("n{} [label=\"{}\"];", id, label));
        id
    }

    fn add_edge(&mut self, from: usize, to: usize, label: Option<&str>) {
        let edge = if let Some(label) = label {
            format!("n{} -> n{} [label=\"{}\"];", from, to, escape_label(label))
        } else {
            format!("n{} -> n{};", from, to)
        };
        self.edges.push(edge);
    }

    fn walk_expr(&mut self, expr: &Expr) -> usize {
        let label = match &expr.kind {
            ExprKind::Integer(v) => format!("Integer({})", v),
            ExprKind::Float(v) => format!("Float({})", v),
            ExprKind::String(v) => format!("String(\"{}\")", v),
            ExprKind::Symbol(v) => format!("Symbol('{}')", v),
            ExprKind::SelfRef => "SelfRef".to_string(),
            ExprKind::Ident(name) => format!("Ident({})", name),
            ExprKind::UnaryMessage { selector, .. } => {
                format!("UnaryMessage({})", selector)
            }
            ExprKind::BinaryMessage { operator, .. } => {
                format!("BinaryMessage({})", operator)
            }
            ExprKind::KeywordMessage { .. } => "KeywordMessage".to_string(),
            ExprKind::Resend { .. } => "Resend".to_string(),
            ExprKind::DirectedResend { delegate, .. } => {
                format!("DirectedResend({})", delegate)
            }
            ExprKind::Paren(_) => "Paren".to_string(),
            ExprKind::Block { .. } => "Block".to_string(),
            ExprKind::Object { .. } => "Object".to_string(),
            ExprKind::Return(_) => "Return".to_string(),
            ExprKind::Sequence(_) => "Sequence".to_string(),
            ExprKind::Cascade { .. } => "Cascade".to_string(),
            ExprKind::Assignment { kind, .. } => match kind {
                AssignKind::Assign => "Assignment(:=)".to_string(),
                AssignKind::Const => "Assignment(=)".to_string(),
            },
            ExprKind::Comment(c) => match c.kind {
                CommentKind::Line => "Comment(Line)".to_string(),
                CommentKind::Block => "Comment(Block)".to_string(),
            },
            ExprKind::Error(msg) => format!("Error({})", msg),
        };

        let id = self.add_node(&label);

        for (idx, c) in expr.leading_comments.iter().enumerate() {
            let comment_id =
                self.add_node(&format!("LeadingComment({:?})", c.kind));
            self.add_edge(id, comment_id, Some(&format!("comment[{}]", idx)));
        }

        match &expr.kind {
            ExprKind::UnaryMessage { receiver, .. } => {
                let child = self.walk_expr(receiver);
                self.add_edge(id, child, Some("receiver"));
            }
            ExprKind::BinaryMessage {
                receiver, argument, ..
            } => {
                let recv = self.walk_expr(receiver);
                let arg = self.walk_expr(argument);
                self.add_edge(id, recv, Some("receiver"));
                self.add_edge(id, arg, Some("argument"));
            }
            ExprKind::KeywordMessage { receiver, pairs } => {
                let recv = self.walk_expr(receiver);
                self.add_edge(id, recv, Some("receiver"));
                for pair in pairs {
                    let arg = self.walk_expr(&pair.argument);
                    self.add_edge(
                        id,
                        arg,
                        Some(&format!("arg:{}", pair.keyword)),
                    );
                }
            }
            ExprKind::Resend { message } => {
                let msg = self.walk_expr(message);
                self.add_edge(id, msg, Some("message"));
            }
            ExprKind::DirectedResend { message, .. } => {
                let msg = self.walk_expr(message);
                self.add_edge(id, msg, Some("message"));
            }
            ExprKind::Paren(inner) => {
                let inner = self.walk_expr(inner);
                self.add_edge(id, inner, Some("expr"));
            }
            ExprKind::Block { args, body } => {
                if !args.is_empty() {
                    let args_id = self.add_node("Args");
                    self.add_edge(id, args_id, Some("args"));
                    for (i, arg) in args.iter().enumerate() {
                        let arg_id = self.add_node(&format!("Arg({})", arg));
                        self.add_edge(
                            args_id,
                            arg_id,
                            Some(&format!("arg[{}]", i)),
                        );
                    }
                }
                for (i, expr) in body.iter().enumerate() {
                    let child = self.walk_expr(expr);
                    self.add_edge(id, child, Some(&format!("body[{}]", i)));
                }
            }
            ExprKind::Object { slots, body } => {
                for (i, slot) in slots.iter().enumerate() {
                    let slot_id = self.walk_slot(slot);
                    self.add_edge(id, slot_id, Some(&format!("slot[{}]", i)));
                }
                for (i, expr) in body.iter().enumerate() {
                    let child = self.walk_expr(expr);
                    self.add_edge(id, child, Some(&format!("body[{}]", i)));
                }
            }
            ExprKind::Return(inner) => {
                let inner = self.walk_expr(inner);
                self.add_edge(id, inner, Some("value"));
            }
            ExprKind::Sequence(exprs) => {
                for (i, expr) in exprs.iter().enumerate() {
                    let child = self.walk_expr(expr);
                    self.add_edge(id, child, Some(&format!("expr[{}]", i)));
                }
            }
            ExprKind::Cascade { receiver, messages } => {
                let recv = self.walk_expr(receiver);
                self.add_edge(id, recv, Some("receiver"));
                for (i, msg) in messages.iter().enumerate() {
                    let child = self.walk_expr(msg);
                    self.add_edge(id, child, Some(&format!("message[{}]", i)));
                }
            }
            ExprKind::Assignment { target, value, .. } => {
                let target = self.walk_expr(target);
                let value = self.walk_expr(value);
                self.add_edge(id, target, Some("target"));
                self.add_edge(id, value, Some("value"));
            }
            ExprKind::Comment(_) | ExprKind::Error(_) => {}
            _ => {}
        }

        id
    }

    fn walk_slot(&mut self, slot: &SlotDescriptor) -> usize {
        let (selector, kind_label) = match &slot.selector {
            SlotSelector::Unary(sel) => (sel.as_str(), "Unary"),
            SlotSelector::Binary(sel) => (sel.as_str(), "Binary"),
            SlotSelector::Keyword(sel) => (sel.as_str(), "Keyword"),
        };
        let mutability = if slot.mutable { "Mutable" } else { "Immutable" };
        let label = if slot.is_parent {
            format!(
                "Slot({}, {}, parent, {})",
                kind_label, mutability, selector
            )
        } else {
            format!("Slot({}, {}, {})", kind_label, mutability, selector)
        };

        let id = self.add_node(&label);
        if !slot.params.is_empty() {
            let args_id = self.add_node("Args");
            self.add_edge(id, args_id, Some("args"));
            for (i, arg) in slot.params.iter().enumerate() {
                let arg_id = self.add_node(&format!("Arg({})", arg));
                self.add_edge(args_id, arg_id, Some(&format!("arg[{}]", i)));
            }
        }
        let value_id = self.walk_expr(&slot.value);
        self.add_edge(id, value_id, Some("value"));
        id
    }
}

fn escape_label(input: &str) -> String {
    let mut out = String::new();
    for ch in input.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            _ => out.push(ch),
        }
    }
    out
}

/// A slot descriptor within an object literal.
#[derive(Debug, Clone, PartialEq)]
pub struct SlotDescriptor {
    pub selector: SlotSelector,
    pub params: Vec<String>,
    pub mutable: bool,
    pub is_parent: bool,
    /// True when this slot came from shorthand syntax (`name.` or `{ name }`).
    pub shorthand: bool,
    pub value: Expr,
    pub span: Span,
    /// Comments that appeared immediately before this slot.
    pub leading_comments: Vec<Comment>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum SlotSelector {
    /// Unary selector: `name`.
    Unary(String),
    /// Binary selector: `+`.
    Binary(String),
    /// Keyword selector: `foo:bar:`.
    Keyword(String),
}
