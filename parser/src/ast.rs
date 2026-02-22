use crate::span::Span;

#[derive(Debug, Clone, PartialEq)]
pub struct Comment {
    pub kind: CommentKind,
    pub text: String,
    pub span: Span,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CommentKind {
    Line,
    Block,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AssignKind {
    Assign,
    Const,
}

#[derive(Debug, Clone, PartialEq)]
pub enum SlotSelector {
    Unary(String),
    Binary(String),
    Keyword(String),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ExprId(pub u32);

#[derive(Debug, Clone, PartialEq)]
pub struct ExprNode {
    pub kind: ExprKind,
    pub span: Span,
    pub leading_comments: Vec<Comment>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum ExprKind {
    Integer(i128),
    Float(f64),
    String(String),
    Symbol(String),
    SelfRef,
    Ident(String),
    UnaryMessage {
        receiver: ExprId,
        selector: String,
        selector_span: Span,
    },
    BinaryMessage {
        receiver: ExprId,
        operator: String,
        operator_span: Span,
        argument: ExprId,
    },
    KeywordMessage {
        receiver: ExprId,
        pairs: Vec<KeywordPair>,
    },
    Resend {
        message: ExprId,
    },
    DirectedResend {
        delegate: String,
        message: ExprId,
    },
    Paren(ExprId),
    Block {
        args: Vec<String>,
        body: Vec<ExprId>,
    },
    Object {
        slots: Vec<SlotDescriptor>,
        body: Vec<ExprId>,
    },
    Return(ExprId),
    Assignment {
        target: ExprId,
        kind: AssignKind,
        value: ExprId,
    },
    Sequence(Vec<ExprId>),
    Cascade {
        receiver: ExprId,
        messages: Vec<ExprId>,
    },
    Comment(Comment),
    Error(String),
}

#[derive(Debug, Clone, PartialEq)]
pub struct KeywordPair {
    pub keyword: String,
    pub keyword_span: Span,
    pub argument: ExprId,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct SlotDescriptor {
    pub selector: SlotSelector,
    pub params: Vec<String>,
    pub mutable: bool,
    pub is_parent: bool,
    pub shorthand: bool,
    pub value: ExprId,
    pub span: Span,
    pub leading_comments: Vec<Comment>,
}

#[derive(Debug, Clone, Default, PartialEq)]
pub struct AstArena {
    nodes: Vec<ExprNode>,
}

impl AstArena {
    pub fn alloc(&mut self, expr: ExprNode) -> ExprId {
        let idx = self.nodes.len();
        self.nodes.push(expr);
        ExprId(idx as u32)
    }

    pub fn get(&self, id: ExprId) -> &ExprNode {
        &self.nodes[id.0 as usize]
    }

    pub fn get_mut(&mut self, id: ExprId) -> &mut ExprNode {
        &mut self.nodes[id.0 as usize]
    }

    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }
}

pub fn to_dot(arena: &AstArena, exprs: &[ExprId]) -> String {
    let mut builder = DotBuilder::new(arena);
    let root = builder.add_node("Program");
    for (idx, expr_id) in exprs.iter().enumerate() {
        let child = builder.walk_expr(*expr_id);
        builder.add_edge(root, child, Some(&format!("expr[{idx}]")));
    }
    builder.finish()
}

struct DotBuilder<'a> {
    arena: &'a AstArena,
    next_id: usize,
    nodes: Vec<String>,
    edges: Vec<String>,
}

impl<'a> DotBuilder<'a> {
    fn new(arena: &'a AstArena) -> Self {
        Self {
            arena,
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
        self.nodes
            .push(format!("n{id} [label=\"{}\"];", escape_label(label)));
        id
    }

    fn add_edge(&mut self, from: usize, to: usize, label: Option<&str>) {
        let edge = if let Some(label) = label {
            format!("n{from} -> n{to} [label=\"{}\"];", escape_label(label))
        } else {
            format!("n{from} -> n{to};")
        };
        self.edges.push(edge);
    }

    fn walk_expr(&mut self, expr_id: ExprId) -> usize {
        let expr = self.arena.get(expr_id);
        let label = match &expr.kind {
            ExprKind::Integer(v) => format!("Integer({v})"),
            ExprKind::Float(v) => format!("Float({v})"),
            ExprKind::String(v) => format!("String(\"{v}\")"),
            ExprKind::Symbol(v) => format!("Symbol('{v}')"),
            ExprKind::SelfRef => "SelfRef".to_string(),
            ExprKind::Ident(name) => format!("Ident({name})"),
            ExprKind::UnaryMessage { selector, .. } => {
                format!("UnaryMessage({selector})")
            }
            ExprKind::BinaryMessage { operator, .. } => {
                format!("BinaryMessage({operator})")
            }
            ExprKind::KeywordMessage { .. } => "KeywordMessage".to_string(),
            ExprKind::Resend { .. } => "Resend".to_string(),
            ExprKind::DirectedResend { delegate, .. } => {
                format!("DirectedResend({delegate})")
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
            ExprKind::Error(msg) => format!("Error({msg})"),
        };

        let id = self.add_node(&label);

        for (idx, c) in expr.leading_comments.iter().enumerate() {
            let comment_id =
                self.add_node(&format!("LeadingComment({:?})", c.kind));
            self.add_edge(id, comment_id, Some(&format!("comment[{idx}]")));
        }

        match &expr.kind {
            ExprKind::UnaryMessage { receiver, .. } => {
                let child = self.walk_expr(*receiver);
                self.add_edge(id, child, Some("receiver"));
            }
            ExprKind::BinaryMessage {
                receiver, argument, ..
            } => {
                let recv = self.walk_expr(*receiver);
                let arg = self.walk_expr(*argument);
                self.add_edge(id, recv, Some("receiver"));
                self.add_edge(id, arg, Some("argument"));
            }
            ExprKind::KeywordMessage { receiver, pairs } => {
                let recv = self.walk_expr(*receiver);
                self.add_edge(id, recv, Some("receiver"));
                for pair in pairs {
                    let arg = self.walk_expr(pair.argument);
                    self.add_edge(
                        id,
                        arg,
                        Some(&format!("arg:{}", pair.keyword)),
                    );
                }
            }
            ExprKind::Resend { message } => {
                let msg = self.walk_expr(*message);
                self.add_edge(id, msg, Some("message"));
            }
            ExprKind::DirectedResend { message, .. } => {
                let msg = self.walk_expr(*message);
                self.add_edge(id, msg, Some("message"));
            }
            ExprKind::Paren(inner) => {
                let inner = self.walk_expr(*inner);
                self.add_edge(id, inner, Some("expr"));
            }
            ExprKind::Block { args, body } => {
                if !args.is_empty() {
                    let args_id = self.add_node("Args");
                    self.add_edge(id, args_id, Some("args"));
                    for (i, arg) in args.iter().enumerate() {
                        let arg_id = self.add_node(&format!("Arg({arg})"));
                        self.add_edge(
                            args_id,
                            arg_id,
                            Some(&format!("arg[{i}]")),
                        );
                    }
                }
                for (i, expr_id) in body.iter().enumerate() {
                    let child = self.walk_expr(*expr_id);
                    self.add_edge(id, child, Some(&format!("body[{i}]")));
                }
            }
            ExprKind::Object { slots, body } => {
                for (i, slot) in slots.iter().enumerate() {
                    let slot_id = self.walk_slot(slot);
                    self.add_edge(id, slot_id, Some(&format!("slot[{i}]")));
                }
                for (i, expr_id) in body.iter().enumerate() {
                    let child = self.walk_expr(*expr_id);
                    self.add_edge(id, child, Some(&format!("body[{i}]")));
                }
            }
            ExprKind::Return(inner) => {
                let inner = self.walk_expr(*inner);
                self.add_edge(id, inner, Some("value"));
            }
            ExprKind::Sequence(exprs) => {
                for (i, expr_id) in exprs.iter().enumerate() {
                    let child = self.walk_expr(*expr_id);
                    self.add_edge(id, child, Some(&format!("expr[{i}]")));
                }
            }
            ExprKind::Cascade { receiver, messages } => {
                let recv = self.walk_expr(*receiver);
                self.add_edge(id, recv, Some("receiver"));
                for (i, msg_id) in messages.iter().enumerate() {
                    let child = self.walk_expr(*msg_id);
                    self.add_edge(id, child, Some(&format!("message[{i}]")));
                }
            }
            ExprKind::Assignment { target, value, .. } => {
                let target = self.walk_expr(*target);
                let value = self.walk_expr(*value);
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
            format!("Slot({kind_label}, {mutability}, parent, {selector})")
        } else {
            format!("Slot({kind_label}, {mutability}, {selector})")
        };

        let id = self.add_node(&label);
        if !slot.params.is_empty() {
            let args_id = self.add_node("Args");
            self.add_edge(id, args_id, Some("args"));
            for (i, arg) in slot.params.iter().enumerate() {
                let arg_id = self.add_node(&format!("Arg({arg})"));
                self.add_edge(args_id, arg_id, Some(&format!("arg[{i}]")));
            }
        }
        let value_id = self.walk_expr(slot.value);
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
