/// Token types produced by the Self lexer.
use crate::span::Span;

/// The kind of a lexical token.
#[derive(Debug, Clone, PartialEq)]
pub enum TokenKind {
    /// Integer literal, e.g. `42`, `-7`, `16rFF`.
    Integer(i64),
    /// Floating-point literal, e.g. `3.14`, `1.5e10`.
    Float(f64),
    /// String literal (contents without surrounding quotes), e.g. `"hello"`.
    String(std::string::String),

    /// A lowercase-starting identifier, e.g. `factorial`, `x`, `_IntAdd`.
    Identifier(std::string::String),
    /// A keyword (identifier + colon), e.g. `at:`, `Put:`, `min:`.
    Keyword(std::string::String),
    /// An argument name (colon + identifier), e.g. `:name`.
    ArgName(std::string::String),

    /// The reserved word `self`.
    SelfKw,
    /// The reserved word `resend`.
    ResendKw,

    /// A binary operator composed of op-chars, e.g. `+`, `<->`, `&&`.
    Operator(std::string::String),
    /// Assignment operator `:=`.
    Assign,

    /// `(`
    LParen,
    /// `)`
    RParen,
    /// `[`
    LBracket,
    /// `]`
    RBracket,
    /// `|` — slot list delimiter.
    Pipe,
    /// `.` — expression separator / slot separator.
    Dot,
    /// `;` — cascade separator.
    Semicolon,
    /// `^` — return operator.
    Caret,
    /// `=` when used as slot initializer (read-only slot).
    Equals,

    /// A line comment: `// ...` (text does NOT include the leading `//`).
    LineComment(std::string::String),
    /// A block comment: `/* ... */` (text does NOT include delimiters).
    /// Block comments may nest.
    BlockComment(std::string::String),

    /// End of input.
    Eof,
    /// An unrecognized character or malformed token.
    Error(std::string::String),
}

impl TokenKind {
    /// Human-readable name for error messages.
    pub fn name(&self) -> &'static str {
        match self {
            Self::Integer(_) => "integer",
            Self::Float(_) => "float",
            Self::String(_) => "string",
            Self::Identifier(_) => "identifier",
            Self::Keyword(_) => "keyword",
            Self::ArgName(_) => "argument name",
            Self::SelfKw => "`self`",
            Self::ResendKw => "`resend`",
            Self::Operator(_) => "operator",
            Self::Assign => "`:=`",
            Self::LParen => "`(`",
            Self::RParen => "`)`",
            Self::LBracket => "`[`",
            Self::RBracket => "`]`",
            Self::Pipe => "`|`",
            Self::Dot => "`.`",
            Self::Semicolon => "`;`",
            Self::Caret => "`^`",
            Self::Equals => "`=`",
            Self::LineComment(_) => "line comment",
            Self::BlockComment(_) => "block comment",
            Self::Eof => "end of input",
            Self::Error(_) => "error",
        }
    }

    /// Returns `true` if this token is any kind of comment.
    pub fn is_comment(&self) -> bool {
        matches!(self, Self::LineComment(_) | Self::BlockComment(_))
    }
}

/// A token with its source span.
#[derive(Debug, Clone, PartialEq)]
pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
    /// The original source text of this token.
    pub lexeme: std::string::String,
}

impl Token {
    pub fn new(
        kind: TokenKind,
        span: Span,
        lexeme: impl Into<std::string::String>,
    ) -> Self {
        Self {
            kind,
            span,
            lexeme: lexeme.into(),
        }
    }

    pub fn is_eof(&self) -> bool {
        matches!(self.kind, TokenKind::Eof)
    }

    pub fn is_comment(&self) -> bool {
        self.kind.is_comment()
    }
}
