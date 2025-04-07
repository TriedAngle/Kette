use crate::{ByteArray, Context, Tagged};

pub struct Parser<'a> {
    input: &'a str,
    position: usize,
}

impl<'a> Parser<'a> {
    pub fn new(input: &'a str) -> Self {
        Parser { input, position: 0 }
    }

    fn skip_whitespace(&mut self) {
        while self.position < self.input.len()
            && self.input[self.position..]
                .chars()
                .next()
                .unwrap()
                .is_whitespace()
        {
            self.position += 1;
        }
    }

    pub fn read_next(&mut self, ctx: &mut Context) -> Tagged {
        self.skip_whitespace();

        if self.position >= self.input.len() {
            return Tagged::ffalse();
        }

        let start = self.position;

        while self.position < self.input.len()
            && !self.input[self.position..]
                .chars()
                .next()
                .unwrap()
                .is_whitespace()
        {
            self.position += 1;
        }

        if start == self.position {
            panic!("Unexpected end of input");
        }

        let token = &self.input[start..self.position];

        ctx.gc.allocate_string(token)
    }

    pub fn parse_int(&self, token_tagged: Tagged) -> Option<Tagged> {
        let token_ptr = token_tagged.to_ptr() as *const ByteArray;
        let token = unsafe { (*token_ptr).as_str() };

        match token.parse::<i64>() {
            Ok(value) => Some(Tagged::from_int(value)),
            Err(_) => None,
        }
    }

    pub fn parse_word(&self, ctx: &Context, token_tagged: Tagged) -> Option<Tagged> {
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

        if let Some(int_value) = self.parse_int(token_tagged) {
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

    pub fn parse_until(&mut self, ctx: &mut Context, delimiter: Option<&str>) -> Vec<Tagged> {
        let mut result = Vec::new();

        self.skip_whitespace();

        while self.position < self.input.len() {
            if let Some(delim) = delimiter {
                if self.input[self.position..].starts_with(delim) {
                    self.position += delim.len();
                    break;
                }
            }

            let token = self.parse_token(ctx);

            if ctx.is_word(token) && ctx.is_parsing_word(token) {
                if let Some(func) = ctx.word_primitive_parse(token) {
                    func(ctx, self)
                } else {
                    let word = token.to_ptr() as _;
                    ctx.execute_word(word);
                }
            } else {
                result.push(token);
            }

            self.skip_whitespace();
        }

        result
    }

    pub fn parse_string(&mut self, ctx: &mut Context) -> Tagged {
        let items = self.parse_until(ctx, None);
        ctx.gc.allocate_quotation(&items)
    }
}

impl Context {
    pub fn parse(&mut self, input: &str) -> Tagged {
        let mut parser = Parser::new(input);
        parser.parse_string(self)
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use parking_lot::Mutex;

    use super::*;
    use crate::{CodeHeap, Context, ContextConfig};

    fn setup_context() -> Context {
        let code_heap = Arc::new(Mutex::new(CodeHeap::new()));
        let config = ContextConfig {
            data_size: 100,
            retian_size: 100,
            name_size: 100,
        };
        Context::new(&config, code_heap)
    }

    #[test]
    fn test_parse_integers() {
        let mut parser = Parser::new("123 -456 0");
        let mut ctx = setup_context();

        let token = parser.read_next(&mut ctx);
        let result = parser.parse_int(token).unwrap();
        assert_eq!(result.to_int(), 123);

        let token = parser.read_next(&mut ctx);
        let result = parser.parse_int(token).unwrap();
        assert_eq!(result.to_int(), -456);

        let token = parser.read_next(&mut ctx);
        let result = parser.parse_int(token).unwrap();
        assert_eq!(result.to_int(), 0);
    }

    #[test]
    fn test_read_next() {
        let mut parser = Parser::new("hello world");
        let mut ctx = setup_context();

        let token1 = parser.read_next(&mut ctx);
        let token1_ptr = token1.to_ptr() as *const ByteArray;
        let token1_str = unsafe { (*token1_ptr).as_str() };
        assert_eq!(token1_str, "hello");

        let token2 = parser.read_next(&mut ctx);
        let token2_ptr = token2.to_ptr() as *const ByteArray;
        let token2_str = unsafe { (*token2_ptr).as_str() };
        assert_eq!(token2_str, "world");
    }

    #[test]
    fn test_parse_until() {
        let mut parser = Parser::new("123 456 789");
        let mut ctx = setup_context();

        let results = parser.parse_until(&mut ctx, None);

        assert_eq!(results.len(), 3);
        assert_eq!(results[0].to_int(), 123);
        assert_eq!(results[1].to_int(), 456);
        assert_eq!(results[2].to_int(), 789);
    }
}
