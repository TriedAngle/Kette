use core::panic;

use crate::{Array, ByteArray, Context, ObjectHeader, Tagged, Word};

pub struct Parser {
    _header: ObjectHeader,
    input: Tagged,    // Points to a ByteArray
    position: Tagged, // Fixnum
}

impl Parser {
    pub fn reset(&mut self, input: Tagged) {
        self.input = input;
        self.position = Tagged::from_int(0);
    }

    fn get_input_bytearray(&self) -> *const ByteArray {
        self.input.to_ptr() as *const ByteArray
    }

    fn current_char(&self) -> Option<char> {
        let pos = self.position.to_int() as usize;
        let input_ptr = self.get_input_bytearray();
        let input_len = unsafe { (*input_ptr).len() };

        if pos >= input_len {
            return None;
        }

        let byte = unsafe { (*input_ptr).get_byte(pos) };
        Some(byte as char)
    }

    fn remaining_slice(&self) -> &str {
        let pos = self.position.to_int() as usize;
        let input_ptr = self.get_input_bytearray();
        let input_str = unsafe { (*input_ptr).as_str() };

        if pos >= input_str.len() {
            return "";
        }

        &input_str[pos..]
    }

    pub fn skip_whitespace(&mut self) {
        while let Some(c) = self.current_char() {
            if !c.is_whitespace() {
                break;
            }
            let new_pos = self.position.to_int() + 1;
            self.position = Tagged::from_int(new_pos);
        }
    }

    fn advance_position(&mut self, by: i64) {
        let new_pos = self.position.to_int() + by;
        self.position = Tagged::from_int(new_pos);
    }

    fn input_len(&self) -> usize {
        let input_ptr = self.get_input_bytearray();
        unsafe { (*input_ptr).len() - 1 }
    }

    fn position_usize(&self) -> usize {
        self.position.to_int() as usize
    }

    fn is_at_end(&self) -> bool {
        self.position_usize() >= self.input_len()
    }

    pub fn read_next(&mut self, ctx: &mut Context) -> Tagged {
        self.skip_whitespace();

        if self.is_at_end() {
            return Tagged::ffalse();
        }

        let start_pos = self.position_usize();

        while !self.is_at_end() {
            if let Some(c) = self.current_char() {
                if c.is_whitespace() {
                    break;
                }
            } else {
                break;
            }
            self.advance_position(1);
        }

        if start_pos == self.position_usize() {
            panic!("Unexpected end of input");
        }

        let input_ptr = self.get_input_bytearray();
        let input_str = unsafe { (*input_ptr).as_str() };
        let token = &input_str[start_pos..self.position_usize()];

        ctx.gc.allocate_string(token)
    }

    pub fn parse_int(token_tagged: Tagged) -> Option<Tagged> {
        let token_ptr = token_tagged.to_ptr() as *const ByteArray;
        let token = unsafe { (*token_ptr).as_str() };

        match token.parse::<i64>() {
            Ok(value) => Some(Tagged::from_int(value)),
            Err(_) => None,
        }
    }

    pub fn parse_word(
        &self,
        ctx: &Context,
        token_tagged: Tagged,
    ) -> Option<Tagged> {
        let (word, _value) = ctx.lookup(token_tagged);

        if word.is_false() {
            return None;
        }

        if !ctx.is_word(word) {
            return None;
        }

        Some(word)
    }

    pub fn parse_token(&mut self, ctx: &mut Context) -> Tagged {
        let token_tagged = self.read_next(ctx);

        if token_tagged.is_false() {
            return token_tagged;
        }

        if let Some(int_value) = Self::parse_int(token_tagged) {
            return int_value;
        }

        if let Some(word) = self.parse_word(ctx, token_tagged) {
            return word;
        } else {
            let raw = token_tagged.to_ptr() as *const ByteArray;
            let value = unsafe { (*raw).as_str() };
            panic!("Parse error, unknown word: {:?}", value);
        }
    }

    pub fn starts_with(&self, prefix: &str) -> bool {
        self.remaining_slice().starts_with(prefix)
    }

    pub fn parse_until(
        &mut self,
        ctx: &mut Context,
        delimiter: Option<&str>,
    ) -> Tagged {
        let mut accum = ctx.gc.allocate_array(100);
        let mut found = !delimiter.is_some();
        self.skip_whitespace();

        while !self.is_at_end() {
            if let Some(delim) = delimiter {
                if self.starts_with(delim) {
                    self.advance_position(delim.len() as i64);
                    found = true;
                    break;
                }
            }

            let token = self.parse_token(ctx);

            if ctx.is_word(token) && ctx.is_parsing_word(token) {
                let word = token.to_ptr() as *mut Word;
                ctx.push(accum);
                ctx.execute_word(word);
                accum = ctx.pop();
            } else {
                let mut arr = accum.to_ptr() as *mut Array;
                if unsafe { (*arr).is_full() } {
                    let new_cap = unsafe { (*arr).capacity() * 2 };
                    let new = ctx.gc.resize_array(accum, new_cap);
                    accum = new;
                    arr = new.to_ptr() as _;
                }
                unsafe { (*arr).push(token) };
            }

            self.skip_whitespace();
        }
        if !found {
            panic!("parse until could not find: {:?}", delimiter);
        }

        accum
    }

    pub fn parse_next(&mut self, ctx: &mut Context) {
        self.skip_whitespace();

        while !self.is_at_end() {
            let token = self.parse_token(ctx);

            if ctx.is_word(token) && ctx.is_parsing_word(token) {
                let accum = ctx.gc.allocate_array(100);
                let word = token.to_ptr() as *mut Word;
                ctx.push(accum);
                ctx.execute_word(word);
            } else {
                ctx.push(token);
            }

            self.skip_whitespace();
        }
    }

    pub fn read_until(
        &mut self,
        ctx: &mut Context,
        stop_sequence: &str,
    ) -> Tagged {
        if self.is_at_end() {
            return Tagged::ffalse();
        }

        let start_pos = self.position_usize();
        let input_ptr = self.get_input_bytearray();
        let input_str = unsafe { (*input_ptr).as_str() };

        let remaining = &input_str[start_pos..];

        if let Some(end_index) = remaining.find(stop_sequence) {
            let end_pos = start_pos + end_index;

            let content = &input_str[start_pos..end_pos];

            self.position = Tagged::from_int(
                (start_pos + end_index + stop_sequence.len()) as i64,
            );

            return ctx.gc.allocate_string(content);
        } else {
            let content = &input_str[start_pos..];

            self.position = Tagged::from_int(input_str.len() as i64);

            return ctx.gc.allocate_string(content);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{CodeHeap, Context, ContextConfig};
    use parking_lot::Mutex;
    use std::sync::Arc;

    fn setup_context() -> Context {
        let code_heap = Arc::new(Mutex::new(CodeHeap::new()));
        let config = ContextConfig {
            data_size: 100,
            retian_size: 100,
            name_size: 100,
            call_size: 100,
            handler_size: 100,
        };
        Context::new(&config, code_heap)
    }

    #[test]
    fn test_parse_integers() {
        let mut ctx = setup_context();
        ctx.reset_parser_string("123 -456 0");

        let token = ctx.read_next();
        let result = Parser::parse_int(token).unwrap();
        assert_eq!(result.to_int(), 123);

        let token = ctx.read_next();
        let result = Parser::parse_int(token).unwrap();
        assert_eq!(result.to_int(), -456);

        let token = ctx.read_next();
        let result = Parser::parse_int(token).unwrap();
        assert_eq!(result.to_int(), 0);
    }

    #[test]
    fn test_read_next() {
        let mut ctx = setup_context();
        ctx.reset_parser_string("hello world");

        let token1 = ctx.read_next();
        let token1_ptr = token1.to_ptr() as *const ByteArray;
        let token1_str = unsafe { (*token1_ptr).as_str() };
        assert_eq!(token1_str, "hello");

        let token2 = ctx.read_next();
        let token2_ptr = token2.to_ptr() as *const ByteArray;
        let token2_str = unsafe { (*token2_ptr).as_str() };
        assert_eq!(token2_str, "world");

        let eof_token = ctx.read_next();
        assert!(eof_token.is_false());
    }

    #[test]
    fn test_parse_until() {
        let mut ctx = setup_context();
        ctx.reset_parser_string("123 456 789");

        let result = ctx.parse_until(None);
        let array = result.to_ptr() as *mut Array;
        let results = unsafe { (*array).as_slice_len() };
        assert_eq!(results.len(), 3);
        assert_eq!(results[0].to_int(), 123);
        assert_eq!(results[1].to_int(), 456);
        assert_eq!(results[2].to_int(), 789);
    }

    #[test]
    fn test_parse_until_with_delimiter() {
        let mut ctx = setup_context();
        ctx.reset_parser_string("123 456 ; 789");

        let result = ctx.parse_until(Some(";"));
        let array = result.to_ptr() as *mut Array;
        let results = unsafe { (*array).as_slice_len() };

        assert_eq!(results.len(), 2);
        assert_eq!(results[0].to_int(), 123);
        assert_eq!(results[1].to_int(), 456);

        let remaining = ctx.read_next();
        let remaining_ptr = remaining.to_ptr() as *const ByteArray;
        let remaining_str = unsafe { (*remaining_ptr).as_str() };
        assert_eq!(remaining_str, "789");
    }

    #[test]
    fn test_read_until() {
        let mut ctx = setup_context();

        ctx.reset_parser_string("Hello, world\" remaining text");

        let result = ctx.read_until("\"");
        let result_ptr = result.to_ptr() as *const ByteArray;
        let result_str = unsafe { (*result_ptr).as_str() };

        assert_eq!(result_str, "Hello, world");

        let remaining = ctx.read_next();
        let remaining_ptr = remaining.to_ptr() as *const ByteArray;
        let remaining_str = unsafe { (*remaining_ptr).as_str() };

        assert_eq!(remaining_str, "remaining");
    }

    #[test]
    fn test_read_until_with_whitespace() {
        let mut ctx = setup_context();

        ctx.reset_parser_string("This is a comment\nNext line");

        let result = ctx.read_until("\n");
        let result_ptr = result.to_ptr() as *const ByteArray;
        let result_str = unsafe { (*result_ptr).as_str() };

        assert_eq!(result_str, "This is a comment");

        let next_line = ctx.read_next();
        let next_line_ptr = next_line.to_ptr() as *const ByteArray;
        let next_line_str = unsafe { (*next_line_ptr).as_str() };

        assert_eq!(next_line_str, "Next");
    }

    #[test]
    fn test_read_until_end_of_input() {
        let mut ctx = setup_context();

        ctx.reset_parser_string("This text has no stop sequence");

        let result = ctx.read_until("not found");
        let result_ptr = result.to_ptr() as *const ByteArray;
        let result_str = unsafe { (*result_ptr).as_str() };

        assert_eq!(result_str, "This text has no stop sequence");

        let eof = ctx.read_next();
        assert!(eof.is_false());
    }

    #[test]
    fn test_read_until_empty_string() {
        let mut ctx = setup_context();

        ctx.reset_parser_string("");

        let result = ctx.read_until("stop");
        assert!(result.is_false());
    }
}
