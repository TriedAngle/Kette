use std::{mem, num::IntErrorKind, sync::Arc};

use crate::{
    Handle, Header, HeaderFlags, HeapObject, HeapProxy, LookupResult, Object,
    ObjectType, Selector, SlotHelper, SlotMap, SlotTags, Tagged, VMProxy,
    Visitable, VisitedLink, executable::ParserObject,
};

#[repr(C)]
#[derive(Debug)]
pub struct Parser {
    pub header: Header,
    pub map: Tagged<SlotMap>,
    pub code: Arc<[u8]>,
    pub end: usize,
    pub offset: usize,
}

#[derive(Debug, Copy, Clone)]
pub struct Token {
    start: usize,
    len: usize,
}

#[derive(Debug, Copy, Clone)]
pub enum ParsedToken {
    Identifier(Token),
    String(Token),
    Fixnum(i64),
    Float(f64),
}

impl Parser {
    #[inline]
    pub fn new(code: &[u8]) -> Self {
        let end = code.len();
        let header =
            Header::encode_object(ObjectType::Slot, 0, HeaderFlags::empty(), 0);
        let map = Tagged::new_ptr(std::ptr::null_mut());

        Self {
            header,
            map,
            code: Arc::from(code),
            end,
            offset: 0,
        }
    }

    #[inline]
    pub fn new_object(vm: &VMProxy, heap: &mut HeapProxy, code: &[u8]) -> Self {
        let end = code.len();
        let header =
            Header::encode_object(ObjectType::Slot, 0, HeaderFlags::empty(), 0);

        let map = heap.allocate_slot_map_helper(
            &vm.shared.strings,
            &[
                SlotHelper::primitive_message("parse-next", SlotTags::empty()),
                SlotHelper::primitive_message("parse-until", SlotTags::empty()),
                SlotHelper::primitive_message("parse-full", SlotTags::empty()),
            ],
        );

        Self {
            header,
            map,
            code: Arc::from(code),
            end,
            offset: 0,
        }
    }

    #[inline]
    pub fn is_done(&self) -> bool {
        self.offset == self.end
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
            self.offset += 1;
        }
    }

    #[inline]
    pub fn next_token(&mut self) -> Option<Token> {
        self.skip_whitespace();
        if self.is_done() {
            return None;
        }

        let start = self.offset;

        if self.is_at_quotes() {
            self.offset += 1;
            while !self.is_done() && !self.is_at_quotes() {
                self.offset += 1;
            }
            self.offset += 1;

            let len = self.offset - start;

            let token = Token { start, len };

            return Some(token);
        }

        while !self.is_done() && !self.is_at_whitespace() {
            self.offset += 1;
        }

        let len = self.offset - start;

        let token = Token { start, len };

        Some(token)
    }

    #[inline]
    pub fn get_token_string(&self, token: Token) -> &str {
        let end = token.start + token.len;
        let ident_bytes = &self.code[token.start..end];
        str::from_utf8(ident_bytes).expect("Code must be utf8")
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
            let token = Token {
                start: token.start + 1,
                len: token.len - 2,
            };
            return Some(ParsedToken::String(token));
        }

        // TODO: handle bignum promotion
        let parsed = if let Ok(fixnum) = self.fixnum_token(string) {
            ParsedToken::Fixnum(fixnum as i64)
        } else if let Some(float) = self.float_token(string) {
            ParsedToken::Float(float)
        } else {
            ParsedToken::Identifier(token)
        };

        Some(parsed)
    }
}

impl Visitable for Parser {}
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
    fn heap_size(&self) -> usize {
        mem::size_of::<Self>()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse_all<'code>(code: &'code str) -> (Parser, Vec<ParsedToken>) {
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
            ParsedToken::Fixnum(n) => assert_eq!(n, 123),
            _ => panic!("Expected Fixnum"),
        }
    }

    #[test]
    fn test_float_token() {
        let (_p, v) = parse_all("3.14");
        match v[0] {
            ParsedToken::Float(f) => assert!((f - 3.14).abs() < 1e-12),
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
            ParsedToken::Fixnum(n) => assert_eq!(n, 123),
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
            ParsedToken::Float(f) => assert!((f - 7.5).abs() < 1e-12),
            _ => panic!("Expected Float"),
        }
    }
}
