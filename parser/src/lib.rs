//! # Parser
//!
//! A streaming lexer and parser for expression syntax.
//!
//! ## Architecture
//!
//! ```text
//!  impl Read (file, socket, &[u8], …)
//!      │
//!      ▼
//!  ┌────────┐    Token stream     ┌────────┐    Expr stream
//!  │ Lexer  │ ──────────────────▶ │ Parser │ ──────────────────▶
//!  └────────┘  (impl Iterator)    └────────┘  (impl Iterator)
//! ```
//!
//! ```rust
//! use parser::{Lexer, Parser};
//!
//! let source = "5 factorial + 3";
//! let lexer = Lexer::from_str(source);
//! let parser = Parser::new(lexer);
//!
//! for result in parser {
//!     match result {
//!         Ok(expr) => println!("{:#?}", expr),
//!         Err(err) => eprintln!("Parse error: {}", err),
//!     }
//! }
//! ```
//!
//! ## Streaming from a network socket
//!
//! ```rust, ignore
//! use std::net::TcpStream;
//! use parser::{Lexer, Parser};
//!
//! let stream = TcpStream::connect("127.0.0.1:9999").unwrap();
//! let lexer = Lexer::new(stream);
//! let parser = Parser::new(lexer);
//!
//! for result in parser {
//!     // Process expressions as they arrive over the wire…
//! }
//! ```

pub mod ast;
pub mod lexer;
pub mod parser;
pub mod semantic;
pub mod span;
pub mod token;

pub use ast::{
    Comment, CommentKind, Expr, ExprKind, KeywordPair, SlotDescriptor,
    SlotSelector,
};
pub use lexer::Lexer;
pub use parser::{ParseError, Parser};
pub use span::{Pos, Span};
pub use token::{Token, TokenKind};

#[cfg(test)]
mod tests {
    use crate::ast::*;
    use crate::lexer::Lexer;
    use crate::parser::{ParseError, Parser};

    fn parse(src: &str) -> Vec<Result<Expr, ParseError>> {
        let lexer = Lexer::from_str(src);
        Parser::new(lexer).collect()
    }

    fn parse_ok(src: &str) -> Vec<Expr> {
        parse(src)
            .into_iter()
            .map(|r| r.expect("parse error"))
            .collect()
    }

    fn parse_one(src: &str) -> Expr {
        let mut exprs = parse_ok(src);
        assert_eq!(exprs.len(), 1, "expected 1 expr, got {}", exprs.len());
        exprs.remove(0)
    }

    #[test]
    fn integer() {
        assert!(matches!(parse_one("42").kind, ExprKind::Integer(42)));
    }

    #[test]
    fn large_integer() {
        assert!(matches!(
            parse_one("18446744073709551615").kind,
            ExprKind::Integer(18_446_744_073_709_551_615)
        ));
    }

    #[test]
    fn graphviz_export_basic() {
        let expr = parse_one("1 + 2");
        let dot = crate::ast::to_dot(&[expr]);
        assert!(dot.contains("digraph AST"));
        assert!(
            dot.contains("BinaryMessage(+)")
                || dot.contains("BinaryMessage(+)")
        );
    }

    #[test]
    fn float() {
        assert!(
            matches!(parse_one("3.14").kind, ExprKind::Float(v) if (v - 3.14).abs() < 1e-10)
        );
    }

    #[test]
    fn string() {
        assert!(
            matches!(parse_one(r#""hello""#).kind, ExprKind::String(ref s) if s == "hello")
        );
    }

    #[test]
    fn symbol_literal() {
        assert!(
            matches!(parse_one("'foo").kind, ExprKind::Symbol(ref s) if s == "foo")
        );
        assert!(matches!(
            parse_one("'Core::Math").kind,
            ExprKind::Symbol(ref s) if s == "Core::Math"
        ));
    }

    #[test]
    fn qualified_identifier_with_path_sep() {
        assert!(matches!(
            parse_one("Lib::Nested::Thing").kind,
            ExprKind::Ident(ref s) if s == "Lib::Nested::Thing"
        ));
    }

    #[test]
    fn self_ref() {
        assert!(matches!(parse_one("self").kind, ExprKind::SelfRef));
    }

    #[test]
    fn implicit_unary_from_name() {
        let e = parse_one("foo");
        assert!(matches!(e.kind, ExprKind::Ident(ref name) if name == "foo"));
    }

    #[test]
    fn unary() {
        let e = parse_one("5 factorial");
        assert!(
            matches!(e.kind, ExprKind::UnaryMessage { ref selector, .. } if selector == "factorial")
        );
    }

    #[test]
    fn unary_chain() {
        let e = parse_one("5 factorial print");
        match &e.kind {
            ExprKind::UnaryMessage { receiver, selector } => {
                assert_eq!(selector, "print");
                assert!(matches!(receiver.kind, ExprKind::UnaryMessage { .. }));
            }
            _ => panic!("expected nested unary"),
        }
    }

    #[test]
    fn binary() {
        let e = parse_one("3 + 4");
        match &e.kind {
            ExprKind::BinaryMessage {
                receiver,
                operator,
                argument,
            } => {
                assert!(matches!(receiver.kind, ExprKind::Integer(3)));
                assert_eq!(operator, "+");
                assert!(matches!(argument.kind, ExprKind::Integer(4)));
            }
            _ => panic!("expected binary"),
        }
    }

    #[test]
    fn pipe_is_not_single_operator() {
        let results = parse("1 | 2");
        assert!(results.iter().any(|r| r.is_err()));
    }

    #[test]
    fn binary_same_op_chains() {
        // `1 + 2 + 3` → (1 + 2) + 3
        let e = parse_one("1 + 2 + 3");
        match &e.kind {
            ExprKind::BinaryMessage {
                receiver,
                operator,
                argument,
            } => {
                assert_eq!(operator, "+");
                assert!(matches!(argument.kind, ExprKind::Integer(3)));
                assert!(matches!(
                    receiver.kind,
                    ExprKind::BinaryMessage { .. }
                ));
            }
            _ => panic!("expected binary"),
        }
    }

    #[test]
    fn mixed_binary_ops_precedence() {
        let e = parse_one("3 + 4 * 7");
        match &e.kind {
            ExprKind::BinaryMessage {
                receiver,
                operator,
                argument,
            } => {
                assert_eq!(operator, "+");
                assert!(matches!(receiver.kind, ExprKind::Integer(3)));
                match &argument.kind {
                    ExprKind::BinaryMessage {
                        receiver: inner_recv,
                        operator: inner_op,
                        argument: inner_arg,
                    } => {
                        assert_eq!(inner_op, "*");
                        assert!(matches!(
                            inner_recv.kind,
                            ExprKind::Integer(4)
                        ));
                        assert!(matches!(inner_arg.kind, ExprKind::Integer(7)));
                    }
                    _ => panic!("expected nested binary"),
                }
            }
            _ => panic!("expected binary"),
        }
    }

    #[test]
    fn binary_precedence_left_assoc() {
        let e = parse_one("10 - 6 - 2");
        match &e.kind {
            ExprKind::BinaryMessage {
                receiver,
                operator,
                argument,
            } => {
                assert_eq!(operator, "-");
                assert!(matches!(argument.kind, ExprKind::Integer(2)));
                assert!(matches!(
                    receiver.kind,
                    ExprKind::BinaryMessage { .. }
                ));
            }
            _ => panic!("expected binary"),
        }
    }

    #[test]
    fn cascade_unary_messages() {
        let e = parse_one("3 factorial; print");
        match &e.kind {
            ExprKind::Cascade { receiver, messages } => {
                assert!(matches!(receiver.kind, ExprKind::Integer(3)));
                assert_eq!(messages.len(), 2);
                match &messages[0].kind {
                    ExprKind::UnaryMessage { receiver, selector } => {
                        assert_eq!(selector, "factorial");
                        assert!(matches!(receiver.kind, ExprKind::Integer(3)));
                    }
                    _ => panic!("expected unary"),
                }
                match &messages[1].kind {
                    ExprKind::UnaryMessage { receiver, selector } => {
                        assert_eq!(selector, "print");
                        assert!(matches!(receiver.kind, ExprKind::Integer(3)));
                    }
                    _ => panic!("expected unary"),
                }
            }
            _ => panic!("expected cascade"),
        }
    }

    #[test]
    fn assignment_rhs_can_be_cascade_unary() {
        let e = parse_one("x := 3 factorial; print");
        match &e.kind {
            ExprKind::Assignment {
                target,
                kind,
                value,
            } => {
                assert_eq!(*kind, AssignKind::Assign);
                assert!(matches!(
                    target.kind,
                    ExprKind::Ident(ref name) if name == "x"
                ));
                match &value.kind {
                    ExprKind::Cascade { receiver, messages } => {
                        assert!(matches!(receiver.kind, ExprKind::Integer(3)));
                        assert_eq!(messages.len(), 2);
                    }
                    _ => panic!("expected cascade as assignment RHS"),
                }
            }
            _ => panic!("expected assignment"),
        }
    }

    #[test]
    fn const_assignment_rhs_can_be_cascade() {
        let e = parse_one("x = 3 + 4; print");
        match &e.kind {
            ExprKind::Assignment { kind, value, .. } => {
                assert_eq!(*kind, AssignKind::Const);
                assert!(matches!(value.kind, ExprKind::Cascade { .. }));
            }
            _ => panic!("expected assignment"),
        }
    }

    #[test]
    fn assignment_rhs_keyword_cascade() {
        let e = parse_one("x := obj add: 1; add: 2");
        match &e.kind {
            ExprKind::Assignment { value, .. } => match &value.kind {
                ExprKind::Cascade { receiver, messages } => {
                    assert!(matches!(
                        receiver.kind,
                        ExprKind::Ident(ref name) if name == "obj"
                    ));
                    assert_eq!(messages.len(), 2);
                }
                _ => panic!("expected cascade"),
            },
            _ => panic!("expected assignment"),
        }
    }

    #[test]
    fn unary_higher_than_binary() {
        // `3 factorial + 4` → (3 factorial) + 4
        let e = parse_one("3 factorial + 4");
        assert!(matches!(e.kind, ExprKind::BinaryMessage { .. }));
    }

    #[test]
    fn keyword_lowest_precedence() {
        // `i: 5 factorial + pi sine` → i: ((5 factorial) + (pi sine))
        let e = parse_one("self i: 5 factorial + pi sine");
        match &e.kind {
            ExprKind::KeywordMessage { receiver, pairs } => {
                assert!(matches!(receiver.kind, ExprKind::SelfRef));
                assert_eq!(pairs.len(), 1);
                assert_eq!(pairs[0].keyword, "i:");
                assert!(matches!(
                    pairs[0].argument.kind,
                    ExprKind::BinaryMessage { .. }
                ));
            }
            _ => panic!("expected keyword message"),
        }
    }

    #[test]
    fn keyword_message() {
        let e = parse_one("5 min: 4 Max: 7");
        match &e.kind {
            ExprKind::KeywordMessage { receiver, pairs } => {
                assert!(matches!(receiver.kind, ExprKind::Integer(5)));
                assert_eq!(pairs.len(), 2);
                assert_eq!(pairs[0].keyword, "min:");
                assert_eq!(pairs[1].keyword, "Max:");
            }
            _ => panic!("expected keyword msg"),
        }
    }

    #[test]
    fn keyword_message_lowercase_parts() {
        let e = parse_one("5 min: 4 max: 7");
        match &e.kind {
            ExprKind::KeywordMessage { receiver, pairs } => {
                assert!(matches!(receiver.kind, ExprKind::Integer(5)));
                assert_eq!(pairs.len(), 2);
                assert_eq!(pairs[0].keyword, "min:");
                assert_eq!(pairs[1].keyword, "max:");
            }
            _ => panic!("expected keyword msg"),
        }
    }

    #[test]
    fn keyword_message_with_assignment_args() {
        let e = parse_one("self foo: (x := 1) bar: (y = 2)");
        match &e.kind {
            ExprKind::KeywordMessage { receiver, pairs } => {
                assert!(matches!(receiver.kind, ExprKind::SelfRef));
                assert_eq!(pairs.len(), 2);
                match &pairs[0].argument.kind {
                    ExprKind::Paren(inner) => match &inner.kind {
                        ExprKind::Assignment { kind, .. } => {
                            assert_eq!(*kind, AssignKind::Assign);
                        }
                        _ => panic!("expected assignment"),
                    },
                    _ => panic!("expected paren"),
                }
                match &pairs[1].argument.kind {
                    ExprKind::Paren(inner) => match &inner.kind {
                        ExprKind::Assignment { kind, .. } => {
                            assert_eq!(*kind, AssignKind::Const);
                        }
                        _ => panic!("expected assignment"),
                    },
                    _ => panic!("expected paren"),
                }
            }
            _ => panic!("expected keyword message"),
        }
    }

    #[test]
    fn implicit_keyword_message_chain() {
        let e = parse_one("self min: 4 max: 7");
        match &e.kind {
            ExprKind::KeywordMessage { receiver, pairs } => {
                assert!(matches!(receiver.kind, ExprKind::SelfRef));
                assert_eq!(pairs.len(), 2);
                assert_eq!(pairs[0].keyword, "min:");
                assert_eq!(pairs[1].keyword, "max:");
            }
            _ => panic!("expected keyword message"),
        }
    }

    #[test]
    fn parens() {
        let e = parse_one("(3 + 4)");
        assert!(matches!(e.kind, ExprKind::Paren(_)));
    }

    #[test]
    fn empty_object() {
        let e = parse_one("{}");
        match &e.kind {
            ExprKind::Object { slots, body } => {
                assert!(slots.is_empty());
                assert!(body.is_empty());
            }
            _ => panic!("expected object"),
        }
    }

    #[test]
    fn object_with_slots() {
        let e = parse_one("{ x := 5. y := 10 }");
        match &e.kind {
            ExprKind::Object { slots, body } => {
                assert_eq!(slots.len(), 2);
                assert!(body.is_empty());
            }
            _ => panic!("expected object"),
        }
    }

    #[test]
    fn object_with_single_slot_no_dot() {
        let e = parse_one("{ x = 7 }");
        match &e.kind {
            ExprKind::Object { slots, body } => {
                assert_eq!(slots.len(), 1);
                assert!(body.is_empty());
            }
            _ => panic!("expected object"),
        }
    }

    #[test]
    fn object_with_single_slot_trailing_dot() {
        let e = parse_one("{ x = 7. }");
        match &e.kind {
            ExprKind::Object { slots, body } => {
                assert_eq!(slots.len(), 1);
                assert!(body.is_empty());
            }
            _ => panic!("expected object"),
        }
    }

    #[test]
    fn object_with_mutable_slot_no_dot() {
        let e = parse_one("{ x := 7 }");
        match &e.kind {
            ExprKind::Object { slots, body } => {
                assert_eq!(slots.len(), 1);
                assert!(body.is_empty());
            }
            _ => panic!("expected object"),
        }
    }

    #[test]
    fn object_with_mutable_slot_trailing_dot() {
        let e = parse_one("{ x := 7. }");
        match &e.kind {
            ExprKind::Object { slots, body } => {
                assert_eq!(slots.len(), 1);
                assert!(body.is_empty());
            }
            _ => panic!("expected object"),
        }
    }

    #[test]
    fn object_with_shorthand_slot_no_dot() {
        let e = parse_one("{ x }");
        match &e.kind {
            ExprKind::Object { slots, body } => {
                assert_eq!(slots.len(), 1);
                assert!(body.is_empty());
                assert!(slots[0].mutable);
                assert!(slots[0].shorthand);
                assert!(
                    matches!(slots[0].selector, SlotSelector::Unary(ref s) if s == "x")
                );
                assert!(
                    matches!(slots[0].value.kind, ExprKind::Ident(ref s) if s == "x")
                );
            }
            _ => panic!("expected object"),
        }
    }

    #[test]
    fn object_with_shorthand_slot_trailing_dot() {
        let e = parse_one("{ x. y. }");
        match &e.kind {
            ExprKind::Object { slots, body } => {
                assert_eq!(slots.len(), 2);
                assert!(body.is_empty());
                assert!(slots.iter().all(|s| s.shorthand));
            }
            _ => panic!("expected object"),
        }
    }

    #[test]
    fn shorthand_with_assignment_stays_pure_data_object() {
        let e = parse_one("{ x. y := 1 }");
        match &e.kind {
            ExprKind::Object { slots, body } => {
                assert_eq!(slots.len(), 2);
                assert!(body.is_empty());
                assert!(slots[0].shorthand);
                assert!(matches!(
                    slots[0].selector,
                    SlotSelector::Unary(ref s) if s == "x"
                ));
                assert!(!slots[1].shorthand);
                assert!(matches!(
                    slots[1].selector,
                    SlotSelector::Unary(ref s) if s == "y"
                ));
                assert!(slots[1].mutable);
            }
            _ => panic!("expected object"),
        }
    }

    #[test]
    fn shorthand_not_allowed_in_method_object() {
        let results = parse("{ x. y print }");
        assert!(results.iter().any(|r| {
            r.as_ref().is_err_and(|e| {
                e.message.contains(
                    "shorthand slots are only allowed in pure data objects",
                )
            })
        }));
    }

    #[test]
    fn trailing_ident_after_expression_is_body_not_shorthand() {
        let e = parse_one("{ out := 1. out print. out }");
        match &e.kind {
            ExprKind::Object { slots, body } => {
                assert_eq!(slots.len(), 1);
                assert_eq!(body.len(), 2);
                assert!(
                    matches!(body[1].kind, ExprKind::Ident(ref s) if s == "out")
                );
            }
            _ => panic!("expected object"),
        }
    }

    #[test]
    fn assignments_after_method_expression_stay_in_body() {
        let e = parse_one("{ x := 1. x print. x := 2 }");
        match &e.kind {
            ExprKind::Object { slots, body } => {
                assert_eq!(slots.len(), 1);
                assert_eq!(body.len(), 2);
                assert!(matches!(
                    body[1].kind,
                    ExprKind::Assignment {
                        kind: AssignKind::Assign,
                        ..
                    }
                ));
            }
            _ => panic!("expected object"),
        }
    }

    #[test]
    fn object_slot_value_expression() {
        let e = parse_one("{ x = 7 + 7 }");
        match &e.kind {
            ExprKind::Object { slots, body } => {
                assert_eq!(slots.len(), 1);
                assert!(body.is_empty());
                assert!(matches!(
                    slots[0].value.kind,
                    ExprKind::BinaryMessage { .. }
                ));
            }
            _ => panic!("expected object"),
        }
    }

    #[test]
    fn object_with_slots_and_body() {
        let e = parse_one("{ x = 5. x print }");
        match &e.kind {
            ExprKind::Object { slots, body } => {
                assert_eq!(slots.len(), 1);
                assert_eq!(body.len(), 1);
            }
            _ => panic!("expected object"),
        }
    }

    #[test]
    fn keyword_arg_object_slots_only() {
        let e = parse_one("Object _Extend: o With: { x := 7 }");
        match &e.kind {
            ExprKind::KeywordMessage { pairs, .. } => {
                assert_eq!(pairs.len(), 2);
                match &pairs[1].argument.kind {
                    ExprKind::Object { slots, body } => {
                        assert_eq!(slots.len(), 1);
                        assert!(body.is_empty());
                    }
                    _ => panic!("expected object literal argument"),
                }
            }
            _ => panic!("expected keyword message"),
        }
    }

    #[test]
    fn block() {
        let e = parse_one("[ | k | k print ]");
        match &e.kind {
            ExprKind::Block { args, body } => {
                assert_eq!(args, &["k"]);
                assert_eq!(body.len(), 1);
            }
            _ => panic!("expected block"),
        }
    }

    #[test]
    fn block_with_slot_initializers() {
        let e = parse_one("[ x := 1. y = 2. x ]");
        match &e.kind {
            ExprKind::Block { args, body } => {
                assert!(args.is_empty());
                assert_eq!(body.len(), 3);
                match &body[0].kind {
                    ExprKind::Assignment { kind, .. } => {
                        assert_eq!(*kind, AssignKind::Assign);
                    }
                    _ => panic!("expected assignment"),
                }
                match &body[1].kind {
                    ExprKind::Assignment { kind, .. } => {
                        assert_eq!(*kind, AssignKind::Const);
                    }
                    _ => panic!("expected assignment"),
                }
            }
            _ => panic!("expected block"),
        }
    }

    #[test]
    fn return_expr() {
        let e = parse_one("^ 42");
        assert!(
            matches!(e.kind, ExprKind::Return(ref inner) if matches!(inner.kind, ExprKind::Integer(42)))
        );
    }

    #[test]
    fn assign_expression() {
        let e = parse_one("x := 5");
        match &e.kind {
            ExprKind::Assignment {
                target,
                kind,
                value,
            } => {
                assert_eq!(*kind, AssignKind::Assign);
                assert!(matches!(
                    target.kind,
                    ExprKind::Ident(ref name) if name == "x"
                ));
                assert!(matches!(value.kind, ExprKind::Integer(5)));
            }
            _ => panic!("expected assignment"),
        }
    }

    #[test]
    fn init_expression() {
        let e = parse_one("x = 3");
        match &e.kind {
            ExprKind::Assignment {
                target,
                kind,
                value,
            } => {
                assert_eq!(*kind, AssignKind::Const);
                assert!(matches!(
                    target.kind,
                    ExprKind::Ident(ref name) if name == "x"
                ));
                assert!(matches!(value.kind, ExprKind::Integer(3)));
            }
            _ => panic!("expected assignment"),
        }
    }

    #[test]
    fn directed_resend() {
        let e = parse_one("resend parent foo");
        match &e.kind {
            ExprKind::DirectedResend { delegate, message } => {
                assert_eq!(delegate, "parent");
                assert!(matches!(
                    message.kind,
                    ExprKind::UnaryMessage { ref selector, .. } if selector == "foo"
                ));
                match &message.kind {
                    ExprKind::UnaryMessage { receiver, .. } => {
                        assert!(matches!(receiver.kind, ExprKind::SelfRef));
                    }
                    _ => panic!("expected unary resend message"),
                }
            }
            _ => panic!("expected directed resend"),
        }
    }

    #[test]
    fn resend_unary_message() {
        let e = parse_one("resend self foo");
        match &e.kind {
            ExprKind::Resend { message } => {
                assert!(matches!(
                    message.kind,
                    ExprKind::UnaryMessage { ref selector, .. } if selector == "foo"
                ));
                match &message.kind {
                    ExprKind::UnaryMessage { receiver, .. } => {
                        assert!(matches!(receiver.kind, ExprKind::SelfRef));
                    }
                    _ => panic!("expected unary resend message"),
                }
            }
            _ => panic!("expected resend"),
        }
    }

    #[test]
    fn keyword_after_binary_message() {
        let e = parse_one("10 > 5 ifTrue: [ ]");
        match &e.kind {
            ExprKind::KeywordMessage { receiver, pairs } => {
                assert_eq!(pairs.len(), 1);
                assert_eq!(pairs[0].keyword, "ifTrue:");
                assert!(matches!(
                    pairs[0].argument.kind,
                    ExprKind::Block { .. }
                ));
                assert!(matches!(
                    receiver.kind,
                    ExprKind::BinaryMessage { .. }
                ));
            }
            _ => panic!("expected keyword message"),
        }
    }

    #[test]
    fn return_with_paren_binary() {
        let e = parse_one("^ ( a & b )");
        match &e.kind {
            ExprKind::Return(inner) => match &inner.kind {
                ExprKind::Paren(expr) => match &expr.kind {
                    ExprKind::BinaryMessage {
                        receiver,
                        operator,
                        argument,
                    } => {
                        assert_eq!(operator, "&");
                        assert!(
                            matches!(receiver.kind, ExprKind::Ident(ref name) if name == "a")
                        );
                        assert!(
                            matches!(argument.kind, ExprKind::Ident(ref name) if name == "b")
                        );
                    }
                    _ => panic!("expected binary message"),
                },
                _ => panic!("expected paren"),
            },
            _ => panic!("expected return"),
        }
    }

    #[test]
    fn whitespace_signed_number_is_invalid() {
        assert!(parse("+ 50")[0].is_err());
        assert!(parse("- 50")[0].is_err());
    }

    #[test]
    fn span_tracking() {
        let e = parse_one("42");
        assert_eq!(e.span.start.line, 1);
        assert_eq!(e.span.start.column, 1);
        assert_eq!(e.span.end.column, 3);
    }

    #[test]
    fn multiple_exprs() {
        let exprs = parse_ok("3 + 4. 5 factorial");
        assert_eq!(exprs.len(), 2);
    }

    #[test]
    fn comment_attached_to_expr() {
        let e = parse_one("// doc comment\n42");
        assert!(matches!(e.kind, ExprKind::Integer(42)));
        assert_eq!(e.leading_comments.len(), 1);
        assert_eq!(e.leading_comments[0].kind, CommentKind::Line);
        assert!(e.leading_comments[0].text.contains("doc comment"));
    }

    #[test]
    fn block_comment_attached() {
        let e = parse_one("/* important */ 42");
        assert!(matches!(e.kind, ExprKind::Integer(42)));
        assert_eq!(e.leading_comments.len(), 1);
        assert_eq!(e.leading_comments[0].kind, CommentKind::Block);
    }

    #[test]
    fn trailing_comment_as_node() {
        // A comment after the last expression with no following expr
        // becomes a free-standing Comment node.
        let exprs = parse_ok("42\n// trailing");
        assert_eq!(exprs.len(), 2);
        assert!(matches!(exprs[0].kind, ExprKind::Integer(42)));
        assert!(matches!(exprs[1].kind, ExprKind::Comment(_)));
    }

    #[test]
    fn multiple_comments_attach() {
        let e = parse_one("// first\n// second\n42");
        assert_eq!(e.leading_comments.len(), 2);
    }

    #[test]
    fn comment_in_object_slot() {
        let e = parse_one("{ // doc for x\n x := 5 }");
        match &e.kind {
            ExprKind::Object { slots, .. } => {
                assert_eq!(slots.len(), 1);
                assert_eq!(slots[0].leading_comments.len(), 1);
            }
            _ => panic!("expected object"),
        }
    }

    #[test]
    fn comment_in_code_body() {
        let e = parse_one("[ x = 1. x print /* end */ ]");
        match &e.kind {
            ExprKind::Block { body, .. } => {
                // body should have the expressions and then the trailing comment
                assert!(body.len() >= 1);
                assert!(
                    body.iter().any(|e| matches!(e.kind, ExprKind::Comment(_)))
                );
            }
            _ => panic!("expected block"),
        }
    }
}
