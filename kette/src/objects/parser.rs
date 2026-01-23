use std::{mem, num::IntErrorKind, sync::Arc};

use crate::{
    Allocator, Header, HeapObject, HeapProxy, LookupResult, Object, ObjectKind,
    ObjectType, Selector, SlotHelper, SlotMap, SlotTags, Tagged, VMProxy,
    Visitable, VisitedLink,
};

#[repr(C)]
#[derive(Debug)]
pub struct Parser {
    pub header: Header,
    pub map: Tagged<SlotMap>,
    pub code: Arc<[u8]>,
    pub end: usize,
    pub offset: usize,
    pub line: usize,
    pub column: usize,
}

#[derive(Debug, Copy, Clone)]
pub struct Token {
    start: usize,
    len: usize,
    line: usize,
    column: usize,
}

#[derive(Debug, Copy, Clone)]
pub enum ParsedToken {
    Identifier(Token),
    String(Token),
    Fixnum((i64, Token)),
    Float((f64, Token)),
}

impl Parser {
    #[inline]
    #[must_use]
    pub fn new(code: &[u8]) -> Self {
        let end = code.len();
        let header = Header::new_object(ObjectType::Slot);
        let map = Tagged::new_ptr(std::ptr::null_mut());

        Self {
            header,
            map,
            code: Arc::from(code),
            end,
            offset: 0,
            line: 1,
            column: 1,
        }
    }

    #[inline]
    pub fn new_object(vm: &VMProxy, heap: &mut HeapProxy, code: &[u8]) -> Self {
        let end = code.len();
        let header = Header::new_object(ObjectType::Slot);

        let map = heap.allocate_slot_map_helper(
            &vm.shared.strings,
            &[
                SlotHelper::primitive_message("parseNext", SlotTags::empty()),
                SlotHelper::primitive_message("parseUntil", SlotTags::empty()),
                SlotHelper::primitive_message("parse", SlotTags::empty()),
            ],
        );

        Self {
            header,
            map: map.as_tagged(),
            code: Arc::from(code),
            end,
            offset: 0,
            line: 1,
            column: 1,
        }
    }

    #[inline]
    pub fn is_done(&self) -> bool {
        self.offset == self.end
    }

    #[inline]
    fn advance_char(&mut self) {
        if self.offset < self.end {
            if self.code[self.offset] == b'\n' {
                self.line += 1;
                self.column = 1;
            } else {
                self.column += 1;
            }
            self.offset += 1;
        }
    }

    #[inline]
    pub fn is_at_whitespace(&self) -> bool {
        self.code[self.offset].is_ascii_whitespace()
    }

    #[inline]
    pub fn is_at_quotes(&self) -> bool {
        self.code[self.offset] == b'"'
    }

    #[inline]
    pub fn skip_whitespace(&mut self) {
        while !self.is_done() && self.is_at_whitespace() {
            self.advance_char();
        }
    }

    #[inline]
    pub fn next_token(&mut self) -> Option<Token> {
        self.skip_whitespace();
        if self.is_done() {
            return None;
        }

        let start = self.offset;
        let line = self.line;
        let column = self.column;

        if self.is_at_quotes() {
            // Consume opening quote
            self.advance_char();

            while !self.is_done() && !self.is_at_quotes() {
                // Determine if escaped? For now just simple consume
                // Note: advance_char handles newlines in multi-line strings
                self.advance_char();
            }

            // Consume closing quote if not EOF
            if !self.is_done() {
                self.advance_char();
            }

            let len = self.offset - start;
            return Some(Token {
                start,
                len,
                line,
                column,
            });
        }

        while !self.is_done() && !self.is_at_whitespace() {
            self.advance_char();
        }

        let len = self.offset - start;
        Some(Token {
            start,
            len,
            line,
            column,
        })
    }

    #[inline]
    pub fn get_token_string(&self, token: Token) -> &str {
        let end = token.start + token.len;
        let bytes = &self.code[token.start..end];
        str::from_utf8(bytes).unwrap_or("<invalid utf8>")
    }

    #[inline]
    pub fn fixnum_token(&self, token: &str) -> Result<u64, IntErrorKind> {
        // disable + and - prefixes
        if !token.starts_with(|c: char| c.is_numeric()) {
            return Err(IntErrorKind::InvalidDigit);
        }
        token.parse::<u64>().map_err(|e| *e.kind())
    }

    #[inline]
    pub fn float_token(&self, token: &str) -> Option<f64> {
        // disable + and - prefixes
        if !token.starts_with(|c: char| c.is_numeric()) {
            return None;
        }
        token.parse::<f64>().ok()
    }

    pub fn parse_next(&mut self) -> Option<ParsedToken> {
        let token = self.next_token()?;
        let string = self.get_token_string(token);

        if string.starts_with('"') && string.ends_with('"') {
            // Trim quotes for the ParsedToken payload
            let token = Token {
                start: token.start + 1,
                len: token.len.saturating_sub(2),
                line: token.line,
                column: token.column,
            };
            return Some(ParsedToken::String(token));
        }

        if let Ok(fixnum) = self.fixnum_token(string) {
            Some(ParsedToken::Fixnum((fixnum as i64, token)))
        } else if let Some(float) = self.float_token(string) {
            Some(ParsedToken::Float((float, token)))
        } else {
            Some(ParsedToken::Identifier(token))
        }
    }

    pub fn read_until(&mut self, end: &str) -> Option<Token> {
        if self.is_done() {
            return None;
        }

        let start = self.offset;
        let line = self.line;
        let column = self.column;

        let remaining_bytes = &self.code[start..];
        let remaining_str = std::str::from_utf8(remaining_bytes).ok()?;

        match remaining_str.find(end) {
            Some(relative_index) => {
                // valid token found
                let token = Token {
                    start,
                    len: relative_index,
                    line,
                    column,
                };

                // We must advance char-by-char (or carefully count newlines)
                // to update line/col correctly for the skipped block.
                let advance_amount = relative_index + end.len();
                for _ in 0..advance_amount {
                    self.advance_char();
                }

                Some(token)
            }
            None => None,
        }
    }
}

impl Visitable for Parser {
    #[inline]
    fn visit_edges(&self, _visitor: &impl crate::Visitor) {
        // visitor.visit(self.map.into());
    }

    #[inline]
    fn visit_edges_mut(&mut self, _visitor: &mut impl crate::Visitor) {
        // visitor.visit_mut(self.map.into());
    }
}
impl Object for Parser {
    fn lookup(
        &self,
        _selector: Selector,
        _link: Option<&VisitedLink>,
    ) -> LookupResult {
        // SAFETY: we assume this is safe
        panic!("should be slot map");
        // let map = unsafe { self.map.promote_to_handle() };
        // map.lookup(selector, link)
    }
}
impl HeapObject for Parser {
    const KIND: ObjectKind = ObjectKind::Object;
    const TYPE_BITS: u8 = ObjectType::Slot as u8;
    fn heap_size(&self) -> usize {
        mem::size_of::<Self>()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse_all(code: &str) -> (Parser, Vec<ParsedToken>) {
        let mut p = Parser::new(code.as_bytes());
        let mut out = Vec::new();
        while let Some(t) = p.parse_next() {
            out.push(t);
        }
        (p, out)
    }

    #[test]
    fn test_skip_whitespace_and_is_done() {
        let mut p = Parser::new(b"   foo");
        assert!(!p.is_done());
        p.skip_whitespace();
        assert_eq!(p.offset, 3);
    }

    #[test]
    fn test_identifier_token() {
        let mut p = Parser::new(b"hello");
        let tok = p.parse_next().unwrap();
        match tok {
            ParsedToken::Identifier(t) => {
                assert_eq!(p.get_token_string(t), "hello");
            }
            _ => panic!("Expected identifier"),
        }
        assert!(p.is_done());
    }

    #[test]
    fn test_fixnum_token() {
        let (_p, v) = parse_all("123");
        match v[0] {
            ParsedToken::Fixnum((n, _)) => assert_eq!(n, 123),
            _ => panic!("Expected Fixnum"),
        }
    }

    #[test]
    fn test_float_token() {
        let (_p, v) = parse_all("2.718");
        match v[0] {
            ParsedToken::Float((f, _)) => {
                // Test parsing a floating point number
                const EXPECTED: f64 = 2.718;
                assert!((f - EXPECTED).abs() < 1e-12)
            }
            _ => panic!("Expected Float"),
        }
    }

    #[test]
    fn test_string_token() {
        let (p, v) = parse_all("\"Hello World!\nWow\"");
        match v[0] {
            ParsedToken::String(t) => {
                assert_eq!(p.get_token_string(t), "Hello World!\nWow")
            }
            _ => panic!("Expected identifier"),
        }
    }

    #[test]
    fn test_no_sign_prefix_parsing() {
        let (p, v) = parse_all("-42  +9  -3.5  +1.2");

        match v[0] {
            ParsedToken::Identifier(t) => {
                assert_eq!(p.get_token_string(t), "-42")
            }
            _ => panic!("Expected identifier"),
        }
        match v[1] {
            ParsedToken::Identifier(t) => {
                assert_eq!(p.get_token_string(t), "+9")
            }
            _ => panic!("Expected identifier"),
        }
        match v[2] {
            ParsedToken::Identifier(t) => {
                assert_eq!(p.get_token_string(t), "-3.5")
            }
            _ => panic!("Expected identifier"),
        }
        match v[3] {
            ParsedToken::Identifier(t) => {
                assert_eq!(p.get_token_string(t), "+1.2")
            }
            _ => panic!("Expected identifier"),
        }
    }

    #[test]
    fn test_multiple_tokens() {
        let (p, v) = parse_all("foo 123 \"wow\" bar 7.5");

        match v[0] {
            ParsedToken::Identifier(t) => {
                assert_eq!(p.get_token_string(t), "foo")
            }
            _ => panic!("Expected identifier"),
        }
        match v[1] {
            ParsedToken::Fixnum((n, _)) => assert_eq!(n, 123),
            _ => panic!("Expected Fixnum"),
        }
        match v[2] {
            ParsedToken::String(t) => {
                assert_eq!(p.get_token_string(t), "wow")
            }
            _ => panic!("Expected identifier"),
        }
        match v[3] {
            ParsedToken::Identifier(t) => {
                assert_eq!(p.get_token_string(t), "bar")
            }
            _ => panic!("Expected identifier"),
        }
        match v[4] {
            ParsedToken::Float((f, _)) => assert!((f - 7.5).abs() < 1e-12),
            _ => panic!("Expected Float"),
        }
    }

    #[test]
    fn test_read_until_found() {
        let mut p = Parser::new(b"content to read|END| remaining");

        let token = p.read_until("|END|").expect("Should find marker");
        assert_eq!(p.get_token_string(token), "content to read");

        assert_eq!(p.offset, 20);

        let next = p.next_token().unwrap();
        assert_eq!(p.get_token_string(next), "remaining");
    }

    #[test]
    fn test_read_until_not_found_resets_offset() {
        let code = b"some code without the marker";
        let mut p = Parser::new(code);

        p.offset = 5;
        let original_offset = p.offset;

        let result = p.read_until("MISSING");

        assert!(result.is_none());

        assert_eq!(p.offset, original_offset);
    }

    #[test]
    fn test_read_until_immediate_match() {
        let mut p = Parser::new(b"STOP now");

        let token = p.read_until("STOP").unwrap();

        assert_eq!(token.len, 0);
        assert_eq!(p.get_token_string(token), "");

        assert_eq!(p.offset, 4);
    }
}
