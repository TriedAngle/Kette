/// Streaming lexer for Self language syntax.
///
/// The [`Lexer`] consumes bytes from any [`std::io::Read`] source —
/// a file, a network socket, `stdin`, or an in-memory buffer — and
/// implements [`Iterator`] over [`Token`]s. It tracks byte offset,
/// line, and column for every token it produces.
///
/// # Streaming
///
/// Internally the lexer maintains a small refillable buffer.  Each call
/// to the iterator pulls exactly as many bytes as are needed for the
/// current token, so it works over slow or infinite streams without
/// requiring the entire input in memory.
///
/// # Comment syntax (modified Self)
///
/// | Syntax         | Kind          | Notes                        |
/// |----------------|---------------|------------------------------|
/// | `// …`         | Line comment  | Runs to end of line          |
/// | `/* … */`      | Block comment | **Nestable** (`/* /* */ */`) |
///
/// # String syntax (modified Self)
///
/// Strings are delimited by **double quotes** (`"…"`) instead of the
/// traditional Self single-quote.  The single quote (`'`) is freed for
/// other uses (e.g. symbol literals in a future extension).
use std::io::Read;

use crate::span::{Pos, Span};
use crate::token::{Token, TokenKind};

// ═══════════════════════════════════════════════════════════════════
// Operator character set
// ═══════════════════════════════════════════════════════════════════

/// Characters that may appear in Self binary operators.
///
/// Compared to the original Self spec we **exclude**:
/// - `|` — always the slot-list pipe delimiter
/// - `"` — now the string delimiter
/// - `/` — handled specially because it starts comments (`//`, `/*`)
///
/// `/` is still allowed as an operator character, but the lexer checks
/// for comment starts *before* falling into operator lexing.
fn is_op_char(c: u8) -> bool {
    matches!(
        c,
        b'!' | b'@'
            | b'#'
            | b'$'
            | b'%'
            | b'^'
            | b'&'
            | b'*'
            | b'-'
            | b'+'
            | b'='
            | b'~'
            | b'/'
            | b'?'
            | b'<'
            | b'>'
            | b','
            | b'|'
            | b'\\'
            | b'`'
            | b'\''
    )
}

// ═══════════════════════════════════════════════════════════════════
// Read buffer — one-byte-at-a-time abstraction over Read
// ═══════════════════════════════════════════════════════════════════

/// Small wrapper that gives us `peek()` / `peek_ahead()` / `advance()`
/// over any `Read`, with position tracking.
///
/// We keep a buffer of `LOOKAHEAD` bytes so we can peek ahead
/// without consuming from the underlying reader.  8 bytes is enough
/// to hold two maximum-length UTF-8 characters, which covers the
/// deepest peek-ahead the lexer ever needs.
const LOOKAHEAD: usize = 8;

struct ReadBuf<R: Read> {
    reader: R,
    buf: [u8; LOOKAHEAD],
    /// How many valid bytes are in `buf` starting from index 0.
    filled: usize,
    /// Whether the underlying reader has returned 0 (EOF).
    reader_eof: bool,
    /// Byte offset from the start of the stream (0-based).
    offset: usize,
    /// Current line (1-based).
    line: usize,
    /// Current column (1-based, byte-based).
    column: usize,
}

impl<R: Read> ReadBuf<R> {
    fn new(reader: R) -> Self {
        let mut rb = Self {
            reader,
            buf: [0u8; LOOKAHEAD],
            filled: 0,
            reader_eof: false,
            offset: 0,
            line: 1,
            column: 1,
        };
        rb.fill();
        rb
    }

    /// Top up the buffer from the reader.
    fn fill(&mut self) {
        while !self.reader_eof && self.filled < LOOKAHEAD {
            let mut one = [0u8; 1];
            match self.reader.read(&mut one) {
                Ok(0) => {
                    self.reader_eof = true;
                }
                Ok(_) => {
                    self.buf[self.filled] = one[0];
                    self.filled += 1;
                }
                Err(_) => {
                    self.reader_eof = true;
                }
            }
        }
    }

    /// Current source position.
    fn pos(&self) -> Pos {
        Pos::new(self.offset, self.line, self.column)
    }

    /// Peek at the current byte without consuming.
    fn peek(&self) -> Option<u8> {
        if self.filled > 0 {
            Some(self.buf[0])
        } else {
            None
        }
    }

    /// Peek `n` bytes ahead (0-indexed: `peek_ahead(0)` == `peek()`).
    fn peek_ahead(&self, n: usize) -> Option<u8> {
        if n < self.filled {
            Some(self.buf[n])
        } else {
            None
        }
    }

    /// Consume one byte and return it, updating position tracking.
    fn advance(&mut self) -> Option<u8> {
        if self.filled == 0 {
            return None;
        }
        let b = self.buf[0];
        // Shift buffer left by 1.
        for i in 0..(self.filled - 1) {
            self.buf[i] = self.buf[i + 1];
        }
        self.filled -= 1;
        // Refill from reader.
        self.fill();

        // Update position.
        self.offset += 1;
        if b == b'\n' {
            self.line += 1;
            self.column = 1;
        } else {
            self.column += 1;
        }
        Some(b)
    }

    /// True if there are no more bytes available.
    #[allow(unused)]
    fn is_empty(&self) -> bool {
        self.filled == 0
    }

    /// Decode the leading UTF-8 character from the buffer without consuming it.
    /// Returns `None` if the buffer is empty.
    /// Returns `Some((char, byte_len))` on success.
    /// On invalid UTF-8, returns the Unicode replacement character with len 1.
    fn peek_char(&self) -> Option<(char, usize)> {
        if self.filled == 0 {
            return None;
        }
        let b0 = self.buf[0];
        let (expected_len, first_bits) = match b0 {
            0x00..=0x7F => return Some((b0 as char, 1)),
            0xC0..=0xDF => (2, (b0 & 0x1F) as u32),
            0xE0..=0xEF => (3, (b0 & 0x0F) as u32),
            0xF0..=0xF7 => (4, (b0 & 0x07) as u32),
            _ => return Some(('\u{FFFD}', 1)), // invalid lead byte
        };
        if expected_len > self.filled {
            // Not enough bytes buffered — treat as replacement.
            return Some(('\u{FFFD}', 1));
        }
        let mut codepoint = first_bits;
        for i in 1..expected_len {
            let cont = self.buf[i];
            if cont & 0xC0 != 0x80 {
                return Some(('\u{FFFD}', 1)); // broken continuation
            }
            codepoint = (codepoint << 6) | (cont & 0x3F) as u32;
        }
        match char::from_u32(codepoint) {
            Some(ch) => Some((ch, expected_len)),
            None => Some(('\u{FFFD}', 1)),
        }
    }

    /// Consume one full UTF-8 character, advancing the position.
    /// Returns `None` if the buffer is empty.
    fn advance_char(&mut self) -> Option<(char, usize)> {
        let (ch, len) = self.peek_char()?;
        for _ in 0..len {
            self.advance(); // each call updates offset/line/column
        }
        Some((ch, len))
    }
}

// ═══════════════════════════════════════════════════════════════════
// Lexer
// ═══════════════════════════════════════════════════════════════════

/// A streaming lexer for Self source code.
///
/// Accepts any [`Read`] — files, sockets, pipes, `&[u8]`, `Cursor`, etc.
///
/// ```rust,ignore
/// use std::io::Cursor;
/// use self_parser::Lexer;
///
/// let stream = Cursor::new(b"5 factorial + 3");
/// let lexer = Lexer::new(stream);
/// for token in lexer {
///     println!("{:?}", token);
/// }
/// ```
pub struct Lexer<R: Read> {
    rb: ReadBuf<R>,
    emitted_eof: bool,
}

impl<R: Read> Lexer<R> {
    /// Create a new lexer over the given readable stream.
    pub fn new(reader: R) -> Self {
        Self {
            rb: ReadBuf::new(reader),
            emitted_eof: false,
        }
    }
}

/// Convenience: create a lexer directly from a `&str`.
impl<'a> Lexer<&'a [u8]> {
    /// Create a new lexer from a source string.
    pub fn from_str(source: &'a str) -> Self {
        Self::new(source.as_bytes())
    }
}

impl<R: Read> Lexer<R> {
    /// Current position.
    fn pos(&self) -> Pos {
        self.rb.pos()
    }

    /// Peek current byte.
    fn peek(&self) -> Option<u8> {
        self.rb.peek()
    }

    /// Peek `n` bytes ahead.
    fn peek_ahead(&self, n: usize) -> Option<u8> {
        self.rb.peek_ahead(n)
    }

    /// Consume one byte.
    fn advance(&mut self) -> Option<u8> {
        self.rb.advance()
    }

    /// Peek the next full UTF-8 character (decoded from bytes).
    fn peek_char(&self) -> Option<(char, usize)> {
        self.rb.peek_char()
    }

    /// Consume one full UTF-8 character (1–4 bytes).
    fn advance_char(&mut self) -> Option<(char, usize)> {
        self.rb.advance_char()
    }

    // ───────────────────────────────────────────────────────────
    //  Whitespace
    // ───────────────────────────────────────────────────────────

    fn skip_whitespace(&mut self) {
        while let Some(b) = self.peek() {
            match b {
                b' ' | b'\t' | b'\n' | b'\r' | 0x0B | 0x08 | 0x0C => {
                    self.advance();
                }
                _ => break,
            }
        }
    }

    // ───────────────────────────────────────────────────────────
    //  Comments:  // line   and   /* block (nestable) */
    // ───────────────────────────────────────────────────────────

    /// Lex a line comment (`// ...` to end of line).
    fn lex_line_comment(&mut self) -> Token {
        let start = self.pos();
        self.advance(); // first `/`
        self.advance(); // second `/`
        let mut text = String::new();
        let mut raw = String::from("//");
        loop {
            match self.peek() {
                Some(b'\n') | None => break,
                Some(b) => {
                    raw.push(b as char);
                    text.push(b as char);
                    self.advance();
                }
            }
        }
        let span = Span::new(start, self.pos());
        Token::new(TokenKind::LineComment(text), span, raw)
    }

    /// Lex a block comment (`/* ... */`), supporting nesting.
    fn lex_block_comment(&mut self) -> Token {
        let start = self.pos();
        self.advance(); // `/`
        self.advance(); // `*`
        let mut text = String::new();
        let mut raw = String::from("/*");
        let mut depth: usize = 1;

        loop {
            match self.peek() {
                None => {
                    let span = Span::new(start, self.pos());
                    return Token::new(
                        TokenKind::Error("unterminated block comment".into()),
                        span,
                        raw,
                    );
                }
                Some(b'/') if self.peek_ahead(1) == Some(b'*') => {
                    // Nested open.
                    depth += 1;
                    raw.push('/');
                    raw.push('*');
                    text.push('/');
                    text.push('*');
                    self.advance();
                    self.advance();
                }
                Some(b'*') if self.peek_ahead(1) == Some(b'/') => {
                    depth -= 1;
                    self.advance();
                    self.advance();
                    raw.push('*');
                    raw.push('/');
                    if depth == 0 {
                        break;
                    }
                    text.push('*');
                    text.push('/');
                }
                Some(b) => {
                    raw.push(b as char);
                    text.push(b as char);
                    self.advance();
                }
            }
        }
        let span = Span::new(start, self.pos());
        Token::new(TokenKind::BlockComment(text), span, raw)
    }

    // ───────────────────────────────────────────────────────────
    //  String literals:  "..."
    // ───────────────────────────────────────────────────────────

    /// Lex a string literal delimited by double-quotes.
    ///
    /// Escape sequences: `\\`, `\"`, `\n`, `\t`, `\r`, `\0`.
    fn lex_string(&mut self) -> Token {
        let start = self.pos();
        self.advance(); // consume opening `"`
        let mut value = String::new();
        let mut raw = String::from("\"");
        loop {
            match self.advance() {
                Some(b'"') => {
                    raw.push('"');
                    break;
                }
                Some(b'\\') => {
                    raw.push('\\');
                    match self.advance() {
                        Some(b'n') => {
                            raw.push('n');
                            value.push('\n');
                        }
                        Some(b't') => {
                            raw.push('t');
                            value.push('\t');
                        }
                        Some(b'r') => {
                            raw.push('r');
                            value.push('\r');
                        }
                        Some(b'0') => {
                            raw.push('0');
                            value.push('\0');
                        }
                        Some(b'\\') => {
                            raw.push('\\');
                            value.push('\\');
                        }
                        Some(b'"') => {
                            raw.push('"');
                            value.push('"');
                        }
                        Some(b) => {
                            raw.push(b as char);
                            value.push(b as char);
                        }
                        None => {
                            let span = Span::new(start, self.pos());
                            return Token::new(
                                TokenKind::Error(
                                    "unterminated string escape".into(),
                                ),
                                span,
                                raw,
                            );
                        }
                    }
                }
                Some(b) => {
                    raw.push(b as char);
                    value.push(b as char);
                }
                None => {
                    let span = Span::new(start, self.pos());
                    return Token::new(
                        TokenKind::Error("unterminated string".into()),
                        span,
                        raw,
                    );
                }
            }
        }
        let span = Span::new(start, self.pos());
        Token::new(TokenKind::String(value), span, raw)
    }

    // ───────────────────────────────────────────────────────────
    //  Numbers
    // ───────────────────────────────────────────────────────────

    fn digit_value(b: u8) -> Option<u32> {
        match b {
            b'0'..=b'9' => Some((b - b'0') as u32),
            b'a'..=b'f' => Some(10 + (b - b'a') as u32),
            b'A'..=b'F' => Some(10 + (b - b'A') as u32),
            _ => None,
        }
    }

    /// Lex an integer (with optional base prefix) or float.
    ///
    /// A leading `-` is consumed only if immediately followed by a digit.
    fn lex_number(&mut self) -> Token {
        let start = self.pos();
        let mut raw = String::new();

        // Optional leading minus.
        let negative = if self.peek() == Some(b'-') {
            raw.push('-');
            self.advance();
            true
        } else {
            false
        };

        // Collect initial digit run.
        let mut digits = String::new();
        let mut has_underscore_prefix = false;
        while let Some(b) = self.peek() {
            if b.is_ascii_digit() {
                digits.push(b as char);
                raw.push(b as char);
                self.advance();
            } else if b == b'_' {
                has_underscore_prefix = true;
                raw.push('_');
                self.advance();
            } else {
                break;
            }
        }

        // Check for base prefix: <digits>r or <digits>R
        if matches!(self.peek(), Some(b'r') | Some(b'R'))
            && !digits.is_empty()
            && !has_underscore_prefix
        {
            let base: u32 = match digits.parse() {
                Ok(b) if (2..=16).contains(&b) => b,
                _ => {
                    let span = Span::new(start, self.pos());
                    return Token::new(
                        TokenKind::Error(format!(
                            "invalid number base: {}",
                            digits
                        )),
                        span,
                        raw,
                    );
                }
            };
            raw.push(self.peek().unwrap() as char);
            self.advance(); // consume 'r'/'R'

            let mut saw_digit = false;
            while let Some(b) = self.peek() {
                if b == b'_' {
                    raw.push('_');
                    self.advance();
                    continue;
                }
                if let Some(_v) = Self::digit_value(b) {
                    raw.push(b as char);
                    self.advance();
                    saw_digit = true;
                    continue;
                }
                break;
            }

            let span = Span::new(start, self.pos());

            if !saw_digit {
                return Token::new(
                    TokenKind::Error("missing digits for radix literal".into()),
                    span,
                    raw,
                );
            }

            if let Some(b) = self.peek() {
                if (b as char).is_ascii_alphanumeric() {
                    raw.push(b as char);
                    self.advance();
                    return Token::new(
                        TokenKind::Error(
                            "invalid digit for radix literal".into(),
                        ),
                        Span::new(start, self.pos()),
                        raw,
                    );
                }
            }

            let mut value: i64 = 0;
            let mut after_r = raw.split('r');
            let _ = after_r.next();
            let digits_part = after_r.next().unwrap_or("");
            for ch in digits_part.chars() {
                if ch == '_' {
                    continue;
                }
                let digit = match Self::digit_value(ch as u8) {
                    Some(v) if v < base => v as i64,
                    _ => {
                        return Token::new(
                            TokenKind::Error(
                                "invalid digit for radix literal".into(),
                            ),
                            span,
                            raw,
                        )
                    }
                };
                value = match value
                    .checked_mul(base as i64)
                    .and_then(|v| v.checked_add(digit))
                {
                    Some(v) => v,
                    None => {
                        return Token::new(
                            TokenKind::Error("radix literal overflow".into()),
                            span,
                            raw,
                        )
                    }
                };
            }
            if negative {
                value = -value;
            }
            return Token::new(TokenKind::Integer(value), span, raw);
        }

        // Check for decimal point (float).
        let is_float = if self.peek() == Some(b'.') {
            // Only treat as float if followed by a digit (not `3.factorial`).
            if matches!(self.peek_ahead(1), Some(d) if d.is_ascii_digit()) {
                raw.push('.');
                self.advance();
                while let Some(b) = self.peek() {
                    if b.is_ascii_digit() || b == b'_' {
                        raw.push(b as char);
                        self.advance();
                    } else {
                        break;
                    }
                }
                true
            } else {
                false
            }
        } else {
            false
        };

        // Check for exponent.
        let has_exp = if matches!(self.peek(), Some(b'e') | Some(b'E')) {
            raw.push(self.peek().unwrap() as char);
            self.advance();
            if matches!(self.peek(), Some(b'+') | Some(b'-')) {
                raw.push(self.peek().unwrap() as char);
                self.advance();
            }
            while let Some(b) = self.peek() {
                if b.is_ascii_digit() || b == b'_' {
                    raw.push(b as char);
                    self.advance();
                } else {
                    break;
                }
            }
            true
        } else {
            false
        };

        let span = Span::new(start, self.pos());
        let normalized: String = raw.chars().filter(|c| *c != '_').collect();

        if is_float || has_exp {
            match normalized.parse::<f64>() {
                Ok(v) => Token::new(TokenKind::Float(v), span, raw),
                Err(e) => Token::new(
                    TokenKind::Error(format!("invalid float: {}", e)),
                    span,
                    raw,
                ),
            }
        } else {
            match normalized.parse::<i64>() {
                Ok(v) => Token::new(TokenKind::Integer(v), span, raw),
                Err(e) => Token::new(
                    TokenKind::Error(format!("invalid integer: {}", e)),
                    span,
                    raw,
                ),
            }
        }
    }

    // ───────────────────────────────────────────────────────────
    //  Identifiers, keywords, reserved words
    // ───────────────────────────────────────────────────────────

    /// Lex an identifier, keyword, or reserved word.
    ///
    /// Identifiers start with a lowercase letter (Unicode `Lowercase_Letter`)
    /// or `_`, and continue with any alphanumeric (Unicode) or `_`.
    fn lex_identifier_or_keyword(&mut self) -> Token {
        let start = self.pos();
        let mut raw = String::new();

        // First character already validated by caller.
        while let Some((ch, _)) = self.peek_char() {
            if ch.is_alphanumeric() || ch == '_' {
                self.advance_char();
                raw.push(ch);
            } else {
                break;
            }
        }

        // Check for keyword colon.
        if self.peek() == Some(b':') {
            raw.push(':');
            self.advance();
            let span = Span::new(start, self.pos());
            return Token::new(TokenKind::Keyword(raw.clone()), span, raw);
        }

        let span = Span::new(start, self.pos());
        let kind = match raw.as_str() {
            "self" => TokenKind::SelfKw,
            "resend" => TokenKind::ResendKw,
            _ => TokenKind::Identifier(raw.clone()),
        };
        Token::new(kind, span, raw)
    }

    /// Lex a capitalized identifier or keyword.
    ///
    /// Starts with an uppercase letter (Unicode `Uppercase_Letter`),
    /// continues with any alphanumeric or `_`.
    fn lex_cap_identifier_or_keyword(&mut self) -> Token {
        let start = self.pos();
        let mut raw = String::new();

        while let Some((ch, _)) = self.peek_char() {
            if ch.is_alphanumeric() || ch == '_' {
                self.advance_char();
                raw.push(ch);
            } else {
                break;
            }
        }

        if self.peek() == Some(b':') {
            raw.push(':');
            self.advance();
            let span = Span::new(start, self.pos());
            Token::new(TokenKind::Keyword(raw.clone()), span, raw)
        } else {
            let span = Span::new(start, self.pos());
            Token::new(TokenKind::Identifier(raw.clone()), span, raw)
        }
    }

    /// Lex an argument name: `:identifier`.
    ///
    /// After the colon, the identifier follows the same Unicode rules.
    fn lex_arg_name(&mut self) -> Token {
        let start = self.pos();
        self.advance(); // consume ':'
        let mut raw = String::from(":");

        // The first character after `:` must be a lowercase letter, `_`,
        // or a non-cased alphabetic character (e.g. CJK).
        match self.peek_char() {
            Some((ch, _))
                if ch == '_' || (ch.is_alphabetic() && !ch.is_uppercase()) => {}
            _ => {
                let span = Span::new(start, self.pos());
                return Token::new(
                    TokenKind::Error("expected identifier after `:`".into()),
                    span,
                    raw,
                );
            }
        }

        let mut name = String::new();
        while let Some((ch, _)) = self.peek_char() {
            if ch.is_alphanumeric() || ch == '_' {
                self.advance_char();
                name.push(ch);
                raw.push(ch);
            } else {
                break;
            }
        }

        let span = Span::new(start, self.pos());
        Token::new(TokenKind::ArgName(name), span, raw)
    }

    // ───────────────────────────────────────────────────────────
    //  Operators and the `:=` assignment
    // ───────────────────────────────────────────────────────────

    /// Lex an operator.
    fn lex_operator(&mut self) -> Token {
        let start = self.pos();
        let mut raw = String::new();

        while let Some(b) = self.peek() {
            if is_op_char(b) {
                // Guard: don't swallow a `/` that starts a comment.
                if b == b'/' && !raw.is_empty() {
                    if matches!(self.peek_ahead(1), Some(b'/') | Some(b'*')) {
                        break;
                    }
                }
                raw.push(b as char);
                self.advance();
            } else {
                break;
            }
        }

        let span = Span::new(start, self.pos());

        Token::new(TokenKind::Operator(raw.clone()), span, raw)
    }

    // ───────────────────────────────────────────────────────────
    //  Main dispatch
    // ───────────────────────────────────────────────────────────

    /// Produce the next token from the stream.
    pub fn next_token(&mut self) -> Token {
        self.skip_whitespace();

        let start = self.pos();

        let b = match self.peek() {
            Some(b) => b,
            None => {
                self.emitted_eof = true;
                return Token::new(TokenKind::Eof, Span::point(start), "");
            }
        };

        match b {
            // ── Comments ──────────────────────────────────────
            // Must check BEFORE operator lexing since `/` is an op-char.
            b'/' if self.peek_ahead(1) == Some(b'/') => self.lex_line_comment(),
            b'/' if self.peek_ahead(1) == Some(b'*') => {
                self.lex_block_comment()
            }

            // ── String literals ───────────────────────────────
            b'"' => self.lex_string(),

            // ── Array starts ─────────────────────────────────
            b'@' if self.peek_ahead(1) == Some(b'(') => {
                self.advance();
                self.advance();
                Token::new(
                    TokenKind::ArrayStart,
                    Span::new(start, self.pos()),
                    "@(",
                )
            }
            b'#' if self.peek_ahead(1) == Some(b'(') => {
                self.advance();
                self.advance();
                Token::new(
                    TokenKind::ByteArrayStart,
                    Span::new(start, self.pos()),
                    "#(",
                )
            }

            // ── Delimiters ────────────────────────────────────
            b'(' => {
                self.advance();
                Token::new(TokenKind::LParen, Span::new(start, self.pos()), "(")
            }
            b')' => {
                self.advance();
                Token::new(TokenKind::RParen, Span::new(start, self.pos()), ")")
            }
            b'[' => {
                self.advance();
                Token::new(
                    TokenKind::LBracket,
                    Span::new(start, self.pos()),
                    "[",
                )
            }
            b']' => {
                self.advance();
                Token::new(
                    TokenKind::RBracket,
                    Span::new(start, self.pos()),
                    "]",
                )
            }
            // ── Pipe ──────────────────────────────────────────
            b'|' => {
                if self.peek_ahead(1).map_or(false, is_op_char) {
                    self.lex_operator()
                } else {
                    self.advance();
                    Token::new(
                        TokenKind::Pipe,
                        Span::new(start, self.pos()),
                        "|",
                    )
                }
            }

            // ── Dot ───────────────────────────────────────────
            b'.' => {
                self.advance();
                Token::new(TokenKind::Dot, Span::new(start, self.pos()), ".")
            }

            // ── Semicolon ─────────────────────────────────────
            b';' => {
                self.advance();
                Token::new(
                    TokenKind::Semicolon,
                    Span::new(start, self.pos()),
                    ";",
                )
            }

            // ── Caret (return) ────────────────────────────────
            b'^' => {
                if self
                    .peek_ahead(1)
                    .map_or(false, |c| is_op_char(c) && c != b'^')
                {
                    self.lex_operator()
                } else {
                    self.advance();
                    Token::new(
                        TokenKind::Caret,
                        Span::new(start, self.pos()),
                        "^",
                    )
                }
            }

            // ── Minus: could be negative number or operator ───
            b'-' => {
                if matches!(self.peek_ahead(1), Some(d) if d.is_ascii_digit()) {
                    self.lex_number()
                } else {
                    self.lex_operator()
                }
            }

            // ── Numbers ───────────────────────────────────────
            b'0'..=b'9' => self.lex_number(),

            // ── Identifiers, keywords, reserved words ─────────
            b'a'..=b'z' | b'_' => self.lex_identifier_or_keyword(),

            // ── Capitalized identifiers / cap-keywords ────────
            b'A'..=b'Z' => self.lex_cap_identifier_or_keyword(),

            // ── Assignment `:=` or argument names ─────────────
            b':' => {
                if self.peek_ahead(1) == Some(b'=') {
                    self.advance();
                    self.advance();
                    Token::new(
                        TokenKind::Assign,
                        Span::new(start, self.pos()),
                        ":=",
                    )
                } else {
                    self.lex_arg_name()
                }
            }

            // ── Equals sign ───────────────────────────────────
            b'=' => {
                if self.peek_ahead(1).map_or(false, is_op_char) {
                    self.lex_operator()
                } else {
                    self.advance();
                    Token::new(
                        TokenKind::Equals,
                        Span::new(start, self.pos()),
                        "=",
                    )
                }
            }

            // ── Other operator characters ─────────────────────
            _ if is_op_char(b) => self.lex_operator(),

            // ── Non-ASCII Unicode identifiers ─────────────────
            // Multi-byte UTF-8 lead bytes (0xC0+) that decode to
            // Unicode letters are routed to identifier lexing.
            _ => {
                if let Some((ch, _)) = self.peek_char() {
                    if ch.is_lowercase() {
                        return self.lex_identifier_or_keyword();
                    }
                    if ch.is_uppercase() {
                        return self.lex_cap_identifier_or_keyword();
                    }
                    // Any other Unicode alphabetic (e.g. CJK, etc.)
                    // treated as lowercase-start identifier.
                    if ch.is_alphabetic() {
                        return self.lex_identifier_or_keyword();
                    }
                }
                // Truly unknown character — advance the full codepoint.
                if let Some((ch, _len)) = self.advance_char() {
                    Token::new(
                        TokenKind::Error(format!(
                            "unexpected character: {:?}",
                            ch
                        )),
                        Span::new(start, self.pos()),
                        ch.to_string(),
                    )
                } else {
                    self.advance();
                    Token::new(
                        TokenKind::Error("unexpected byte".into()),
                        Span::new(start, self.pos()),
                        "?",
                    )
                }
            }
        }
    }
}

impl<R: Read> Iterator for Lexer<R> {
    type Item = Token;

    fn next(&mut self) -> Option<Token> {
        if self.emitted_eof {
            return None;
        }
        let tok = self.next_token();
        if tok.is_eof() {
            self.emitted_eof = true;
        }
        Some(tok)
    }
}

// ═══════════════════════════════════════════════════════════════════
// Tests
// ═══════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Cursor;

    fn tokens(src: &str) -> Vec<Token> {
        Lexer::from_str(src).collect()
    }

    fn kinds(src: &str) -> Vec<TokenKind> {
        tokens(src).into_iter().map(|t| t.kind).collect()
    }

    // ── Basic literals ────────────────────────────────────────

    #[test]
    fn lex_integer() {
        assert_eq!(kinds("42"), vec![TokenKind::Integer(42), TokenKind::Eof]);
    }

    #[test]
    fn lex_negative_integer() {
        assert_eq!(kinds("-7"), vec![TokenKind::Integer(-7), TokenKind::Eof]);
    }

    #[test]
    fn lex_based_integer() {
        assert_eq!(
            kinds("16rFF"),
            vec![TokenKind::Integer(255), TokenKind::Eof]
        );
        assert_eq!(
            kinds("2r1010"),
            vec![TokenKind::Integer(10), TokenKind::Eof]
        );
    }

    #[test]
    fn lex_integer_with_underscores() {
        assert_eq!(
            kinds("1_000"),
            vec![TokenKind::Integer(1000), TokenKind::Eof]
        );
        assert_eq!(
            kinds("1__2__3"),
            vec![TokenKind::Integer(123), TokenKind::Eof]
        );
    }

    #[test]
    fn lex_float_with_underscores() {
        assert_eq!(
            kinds("3.14_15"),
            vec![TokenKind::Float(3.1415), TokenKind::Eof]
        );
    }

    #[test]
    fn lex_exp_with_underscores() {
        assert_eq!(
            kinds("1e1__0"),
            vec![TokenKind::Float(1e10), TokenKind::Eof]
        );
    }

    #[test]
    fn lex_radix_with_underscores() {
        assert_eq!(
            kinds("8r7__7"),
            vec![TokenKind::Integer(63), TokenKind::Eof]
        );
        assert_eq!(
            kinds("16rff"),
            vec![TokenKind::Integer(255), TokenKind::Eof]
        );
    }

    #[test]
    fn lex_invalid_radix_digit() {
        let k = kinds("2r2");
        assert!(matches!(k[0], TokenKind::Error(_)));
        let k = kinds("16rG");
        assert!(matches!(k[0], TokenKind::Error(_)));
    }

    #[test]
    fn lex_float() {
        assert_eq!(kinds("3.14"), vec![TokenKind::Float(3.14), TokenKind::Eof]);
    }

    #[test]
    fn lex_float_exp() {
        assert_eq!(kinds("1e10"), vec![TokenKind::Float(1e10), TokenKind::Eof]);
    }

    // ── Strings (double-quoted) ───────────────────────────────

    #[test]
    fn lex_string() {
        assert_eq!(
            kinds(r#""hello""#),
            vec![TokenKind::String("hello".into()), TokenKind::Eof]
        );
    }

    #[test]
    fn lex_string_escapes() {
        assert_eq!(
            kinds(r#""a\nb""#),
            vec![TokenKind::String("a\nb".into()), TokenKind::Eof]
        );
    }

    #[test]
    fn lex_string_escaped_quote() {
        assert_eq!(
            kinds(r#""say \"hi\"""#),
            vec![TokenKind::String("say \"hi\"".into()), TokenKind::Eof]
        );
    }

    // ── Identifiers & keywords ────────────────────────────────

    #[test]
    fn lex_identifiers_and_keywords() {
        assert_eq!(
            kinds("factorial"),
            vec![TokenKind::Identifier("factorial".into()), TokenKind::Eof]
        );
        assert_eq!(
            kinds("at:"),
            vec![TokenKind::Keyword("at:".into()), TokenKind::Eof]
        );
        assert_eq!(
            kinds("Put:"),
            vec![TokenKind::Keyword("Put:".into()), TokenKind::Eof]
        );
    }

    #[test]
    fn lex_reserved() {
        assert_eq!(kinds("self"), vec![TokenKind::SelfKw, TokenKind::Eof]);
        assert_eq!(kinds("resend"), vec![TokenKind::ResendKw, TokenKind::Eof]);
    }

    #[test]
    fn lex_arg_name() {
        assert_eq!(
            kinds(":name"),
            vec![TokenKind::ArgName("name".into()), TokenKind::Eof]
        );
    }

    // ── Operators ─────────────────────────────────────────────

    #[test]
    fn lex_operators() {
        assert_eq!(
            kinds("+"),
            vec![TokenKind::Operator("+".into()), TokenKind::Eof]
        );
        assert_eq!(
            kinds("<->"),
            vec![TokenKind::Operator("<->".into()), TokenKind::Eof]
        );
        assert_eq!(
            kinds("||"),
            vec![TokenKind::Operator("||".into()), TokenKind::Eof]
        );
    }

    #[test]
    fn lex_assign() {
        assert_eq!(kinds(":="), vec![TokenKind::Assign, TokenKind::Eof]);
    }

    #[test]
    fn lex_slash_as_operator() {
        // A lone `/` is a valid operator (not a comment start).
        assert_eq!(
            kinds("3 / 4"),
            vec![
                TokenKind::Integer(3),
                TokenKind::Operator("/".into()),
                TokenKind::Integer(4),
                TokenKind::Eof,
            ]
        );
    }

    // ── Comments ──────────────────────────────────────────────

    #[test]
    fn lex_line_comment() {
        let k = kinds("42 // this is a comment\n7");
        assert_eq!(
            k,
            vec![
                TokenKind::Integer(42),
                TokenKind::LineComment(" this is a comment".into()),
                TokenKind::Integer(7),
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn lex_block_comment() {
        let k = kinds("42 /* comment */ 7");
        assert_eq!(
            k,
            vec![
                TokenKind::Integer(42),
                TokenKind::BlockComment(" comment ".into()),
                TokenKind::Integer(7),
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn lex_nested_block_comment() {
        let k = kinds("/* outer /* inner */ still outer */ 1");
        assert_eq!(
            k,
            vec![
                TokenKind::BlockComment(
                    " outer /* inner */ still outer ".into()
                ),
                TokenKind::Integer(1),
                TokenKind::Eof,
            ]
        );
    }

    // ── Delimiters ────────────────────────────────────────────

    #[test]
    fn lex_delimiters() {
        assert_eq!(
            kinds("( | | )"),
            vec![
                TokenKind::LParen,
                TokenKind::Pipe,
                TokenKind::Pipe,
                TokenKind::RParen,
                TokenKind::Eof,
            ]
        );
    }

    // ── Complex expressions ───────────────────────────────────

    #[test]
    fn lex_complex_expression() {
        let k = kinds("5 min: 4 Max: 7");
        assert_eq!(
            k,
            vec![
                TokenKind::Integer(5),
                TokenKind::Keyword("min:".into()),
                TokenKind::Integer(4),
                TokenKind::Keyword("Max:".into()),
                TokenKind::Integer(7),
                TokenKind::Eof,
            ]
        );
    }

    // ── Span tracking ─────────────────────────────────────────

    #[test]
    fn span_tracking() {
        let toks = tokens("ab cd");
        assert_eq!(toks[0].span.start.line, 1);
        assert_eq!(toks[0].span.start.column, 1);
        assert_eq!(toks[1].span.start.column, 4);
    }

    #[test]
    fn span_multiline() {
        let toks = tokens("a\nb");
        assert_eq!(toks[0].span.start.line, 1);
        assert_eq!(toks[1].span.start.line, 2);
        assert_eq!(toks[1].span.start.column, 1);
    }

    // ── Read-based streaming ──────────────────────────────────

    #[test]
    fn lex_from_cursor() {
        let stream = Cursor::new(b"42 + 1" as &[u8]);
        let toks: Vec<_> = Lexer::new(stream).map(|t| t.kind).collect();
        assert_eq!(
            toks,
            vec![
                TokenKind::Integer(42),
                TokenKind::Operator("+".into()),
                TokenKind::Integer(1),
                TokenKind::Eof,
            ]
        );
    }

    // ── Unicode / UTF-8 identifiers ───────────────────────────

    #[test]
    fn lex_unicode_lowercase_identifier() {
        // German: "größe" (lowercase, multi-byte ö)
        let k = kinds("größe");
        assert_eq!(
            k,
            vec![TokenKind::Identifier("größe".into()), TokenKind::Eof]
        );
    }

    #[test]
    fn lex_unicode_uppercase_identifier() {
        // German: "Über" starts with uppercase Ü
        let k = kinds("Über");
        assert_eq!(
            k,
            vec![TokenKind::Identifier("Über".into()), TokenKind::Eof]
        );
    }

    #[test]
    fn lex_unicode_keyword_uppercase() {
        // Japanese mixed: "Über:" as a keyword
        let k = kinds("Über:");
        assert_eq!(k, vec![TokenKind::Keyword("Über:".into()), TokenKind::Eof]);
    }

    #[test]
    fn lex_unicode_keyword_lowercase() {
        // French: "café:" as a keyword
        let k = kinds("café:");
        assert_eq!(k, vec![TokenKind::Keyword("café:".into()), TokenKind::Eof]);
    }

    #[test]
    fn lex_cjk_identifier() {
        // Chinese characters as an identifier
        let k = kinds("变量");
        assert_eq!(
            k,
            vec![TokenKind::Identifier("变量".into()), TokenKind::Eof]
        );
    }

    #[test]
    fn lex_cyrillic_identifier() {
        let k = kinds("привет");
        assert_eq!(
            k,
            vec![TokenKind::Identifier("привет".into()), TokenKind::Eof]
        );
    }

    #[test]
    fn lex_unicode_arg_name() {
        let k = kinds(":名前");
        assert_eq!(k, vec![TokenKind::ArgName("名前".into()), TokenKind::Eof]);
    }

    #[test]
    fn lex_mixed_ascii_unicode() {
        // Identifier with mixed scripts: "point2D_α"
        let k = kinds("point2D_α");
        assert_eq!(
            k,
            vec![TokenKind::Identifier("point2D_α".into()), TokenKind::Eof]
        );
    }

    #[test]
    fn lex_unicode_in_expression() {
        // Full expression with unicode identifiers
        let k = kinds("größe + länge");
        assert_eq!(
            k,
            vec![
                TokenKind::Identifier("größe".into()),
                TokenKind::Operator("+".into()),
                TokenKind::Identifier("länge".into()),
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn lex_emoji_is_error() {
        // Emoji are not letters — should produce an error token.
        let k = kinds("🎉");
        assert!(matches!(k[0], TokenKind::Error(_)));
    }
}
