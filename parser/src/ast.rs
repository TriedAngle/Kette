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
    Integer(i64),
    /// Floating-point literal.
    Float(f64),
    /// String literal.
    String(String),

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
    },

    /// A binary message send: `receiver op argument`.
    ///
    /// Precedence: table-driven.  Associativity: left-to-right for same op.
    BinaryMessage {
        receiver: Box<Expr>,
        operator: String,
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

    /// A block literal: `[ | slots | code ]`.
    Block {
        args: Vec<String>,
        locals: Vec<SlotDescriptor>,
        body: Vec<Expr>,
    },

    /// An object literal: `( | slots | code )`.
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
    pub argument: Expr,
    pub span: Span,
}

/// The assignment operator kind.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AssignKind {
    /// `:=` (assign to read-write slot).
    Assign,
    /// `=` (initialize read-only slot).
    Init,
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
                AssignKind::Init => "Assignment(=)".to_string(),
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
            ExprKind::Block { args, locals, body } => {
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
                for (i, slot) in locals.iter().enumerate() {
                    let slot_id = self.walk_slot(slot);
                    self.add_edge(id, slot_id, Some(&format!("local[{}]", i)));
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
        let label = match &slot.kind {
            SlotKind::ReadOnly {
                name, is_parent, ..
            } => {
                if *is_parent {
                    format!("Slot(ReadOnly, parent, {})", name)
                } else {
                    format!("Slot(ReadOnly, {})", name)
                }
            }
            SlotKind::ReadWrite {
                name, is_parent, ..
            } => {
                if *is_parent {
                    format!("Slot(ReadWrite, parent, {})", name)
                } else {
                    format!("Slot(ReadWrite, {})", name)
                }
            }
            SlotKind::Argument { name } => format!("Slot(Arg, {})", name),
            SlotKind::Method {
                selector,
                is_parent,
                arguments: _,
                ..
            } => {
                if *is_parent {
                    format!("Slot(Method, parent, {})", selector)
                } else {
                    format!("Slot(Method, {})", selector)
                }
            }
        };

        let id = self.add_node(&label);
        match &slot.kind {
            SlotKind::ReadOnly { initializer, .. }
            | SlotKind::ReadWrite { initializer, .. } => {
                if let Some(init) = initializer {
                    let child = self.walk_expr(init);
                    self.add_edge(id, child, Some("initializer"));
                }
            }
            SlotKind::Method {
                arguments, body, ..
            } => {
                if !arguments.is_empty() {
                    let args_id = self.add_node("Args");
                    self.add_edge(id, args_id, Some("args"));
                    for (i, arg) in arguments.iter().enumerate() {
                        let arg_id = self.add_node(&format!("Arg({})", arg));
                        self.add_edge(
                            args_id,
                            arg_id,
                            Some(&format!("arg[{}]", i)),
                        );
                    }
                }
                let body_id = self.walk_expr(body);
                self.add_edge(id, body_id, Some("body"));
            }
            SlotKind::Argument { .. } => {}
        }
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

/// A slot descriptor within an object or block literal.
#[derive(Debug, Clone, PartialEq)]
pub struct SlotDescriptor {
    pub kind: SlotKind,
    pub span: Span,
    /// Comments that appeared immediately before this slot.
    pub leading_comments: Vec<Comment>,
}

/// The different kinds of slots that can appear in an object literal.
#[derive(Debug, Clone, PartialEq)]
pub enum SlotKind {
    /// Read-only data slot: `name = expr`.
    ReadOnly {
        name: String,
        is_parent: bool,
        initializer: Option<Expr>,
    },
    /// Read-write (assignable) data slot: `name := expr` or bare `name`.
    ReadWrite {
        name: String,
        is_parent: bool,
        initializer: Option<Expr>,
    },
    /// Argument slot: `:name`.
    Argument { name: String },
    /// A slot containing a method.
    Method {
        selector: String,
        is_parent: bool,
        arguments: Vec<String>,
        body: Expr,
    },
}
