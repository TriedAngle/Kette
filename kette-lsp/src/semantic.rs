use parser::{AstArena, ExprId, Token, semantic};
#[cfg(test)]
use parser::{Lexer, Parser, TokenKind};
use tower_lsp::lsp_types::{
    SemanticToken, SemanticTokenModifier, SemanticTokenType,
};

const TYPE_UNARY_METHOD: u32 = 0;
const TYPE_KEYWORD_MESSAGE: u32 = 1;
const TYPE_LOCAL: u32 = 2;
const TYPE_GLOBAL: u32 = 3;
const TYPE_OPERATOR: u32 = 4;
const TYPE_PUNCTUATION: u32 = 5;
const TYPE_LITERAL_NUMBER: u32 = 6;
const TYPE_LITERAL_STRING: u32 = 7;
const TYPE_KEYWORD: u32 = 8;
const TYPE_COMMENT: u32 = 9;
const TYPE_PARAMETER: u32 = 10;

pub fn token_types() -> Vec<SemanticTokenType> {
    vec![
        SemanticTokenType::METHOD,
        SemanticTokenType::FUNCTION,
        SemanticTokenType::VARIABLE,
        SemanticTokenType::NAMESPACE,
        SemanticTokenType::OPERATOR,
        SemanticTokenType::new("punctuation"),
        SemanticTokenType::NUMBER,
        SemanticTokenType::STRING,
        SemanticTokenType::KEYWORD,
        SemanticTokenType::COMMENT,
        SemanticTokenType::PARAMETER,
    ]
}

pub fn token_modifiers() -> Vec<SemanticTokenModifier> {
    Vec::new()
}

#[cfg(test)]
pub fn semantic_tokens(source: &str) -> Vec<SemanticToken> {
    let tokens: Vec<Token> = Lexer::from_str(source)
        .filter(|t| !t.is_eof() && !matches!(t.kind, TokenKind::Error(_)))
        .collect();

    let mut parser = Parser::new(Lexer::from_str(source));
    let parse_results: Vec<_> = parser.by_ref().collect();
    let arena = parser.into_arena();
    let exprs: Vec<ExprId> =
        parse_results.into_iter().filter_map(Result::ok).collect();

    semantic_tokens_from(source, &tokens, &arena, &exprs)
}

pub fn semantic_tokens_from(
    source: &str,
    tokens: &[Token],
    arena: &AstArena,
    exprs: &[ExprId],
) -> Vec<SemanticToken> {
    let spans = semantic::analyze_semantics_ids(tokens, arena, exprs);
    let mut out = Vec::with_capacity(spans.len());
    let mut cursor = OffsetCursor::new(source);
    let mut prev_line = 0u32;
    let mut prev_start = 0u32;

    for span in spans {
        let Some(token_type) = kind_to_type(span.kind) else {
            continue;
        };

        let Some((start_line, start_col)) = cursor.advance_to(span.start)
        else {
            continue;
        };
        let Some(length) = utf16_len_same_line(source, span.start, span.end)
        else {
            continue;
        };
        if length == 0 {
            continue;
        }

        let delta_line = start_line.saturating_sub(prev_line);
        let delta_start = if delta_line == 0 {
            start_col.saturating_sub(prev_start)
        } else {
            start_col
        };

        out.push(SemanticToken {
            delta_line,
            delta_start,
            length,
            token_type,
            token_modifiers_bitset: 0,
        });

        prev_line = start_line;
        prev_start = start_col;
    }

    out
}

struct OffsetCursor<'a> {
    source: &'a str,
    iter: std::str::CharIndices<'a>,
    byte: usize,
    line: u32,
    utf16_col: u32,
}

impl<'a> OffsetCursor<'a> {
    fn new(source: &'a str) -> Self {
        Self {
            source,
            iter: source.char_indices(),
            byte: 0,
            line: 0,
            utf16_col: 0,
        }
    }

    fn advance_to(&mut self, target: usize) -> Option<(u32, u32)> {
        if target < self.byte || target > self.source.len() {
            return None;
        }
        while self.byte < target {
            let (idx, ch) = self.iter.next()?;
            if idx != self.byte {
                return None;
            }
            if ch == '\n' {
                self.line = self.line.saturating_add(1);
                self.utf16_col = 0;
            } else {
                self.utf16_col =
                    self.utf16_col.saturating_add(ch.len_utf16() as u32);
            }
            self.byte = idx + ch.len_utf8();
        }
        Some((self.line, self.utf16_col))
    }
}

fn utf16_len_same_line(source: &str, start: usize, end: usize) -> Option<u32> {
    if end < start || end > source.len() {
        return None;
    }
    let slice = source.get(start..end)?;
    if slice.contains('\n') {
        return None;
    }
    Some(slice.encode_utf16().count() as u32)
}

fn kind_to_type(kind: semantic::SemanticKind) -> Option<u32> {
    Some(match kind {
        semantic::SemanticKind::UnaryMethod => TYPE_UNARY_METHOD,
        semantic::SemanticKind::KeywordMessage => TYPE_KEYWORD_MESSAGE,
        semantic::SemanticKind::Local => TYPE_LOCAL,
        semantic::SemanticKind::Global => TYPE_GLOBAL,
        semantic::SemanticKind::Operator => TYPE_OPERATOR,
        semantic::SemanticKind::Punctuation => TYPE_PUNCTUATION,
        semantic::SemanticKind::LiteralNumber => TYPE_LITERAL_NUMBER,
        semantic::SemanticKind::LiteralString => TYPE_LITERAL_STRING,
        semantic::SemanticKind::Keyword => TYPE_KEYWORD,
        semantic::SemanticKind::Comment => TYPE_COMMENT,
        semantic::SemanticKind::Parameter => TYPE_PARAMETER,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn emits_semantic_tokens_for_kette_categories() {
        let source = "Global := { foo = [ | x | x print ] }. Global foo: 1";
        let tokens = semantic_tokens(source);
        assert!(!tokens.is_empty());
    }

    #[test]
    fn emits_semantic_token_for_symbol_literal() {
        let source = "'Core::Math";
        let tokens = semantic_tokens(source);
        assert_eq!(tokens.len(), 1);
        assert_eq!(tokens[0].token_type, TYPE_GLOBAL);
    }

    #[test]
    fn emits_selfkeyword_token_for_self() {
        let source = "self";
        let tokens = semantic_tokens(source);
        assert!(tokens.iter().any(|tok| tok.token_type == TYPE_KEYWORD));
    }

    #[test]
    fn marks_large_integer_as_number_literal() {
        let source = "18446744073709551615";
        let tokens = semantic_tokens(source);
        assert_eq!(tokens.len(), 1);
        assert_eq!(tokens[0].token_type, TYPE_LITERAL_NUMBER);
    }

    #[test]
    fn marks_keyword_and_binary_slot_params() {
        let source = "{ + rhs = { rhs }. foo: a Bar: b = { a + b } }";
        let tokens = semantic_tokens(source);
        let param_count = tokens
            .iter()
            .filter(|tok| tok.token_type == TYPE_PARAMETER)
            .count();
        assert!(param_count >= 4);
    }

    #[test]
    fn marks_assignment_operators() {
        let source = "{ x := 1. y = 2 }";
        let tokens = semantic_tokens(source);
        let op_count = tokens
            .iter()
            .filter(|tok| tok.token_type == TYPE_OPERATOR)
            .count();
        assert!(op_count >= 2);
    }

    #[test]
    fn marks_punctuation_tokens() {
        let source = "[ | x | { x := 1 } ]";
        let tokens = semantic_tokens(source);
        assert!(tokens.iter().any(|tok| tok.token_type == TYPE_PUNCTUATION));
    }

    #[test]
    fn marks_path_separator_as_punctuation() {
        let source = "Lib::Nested::Greeter";
        let tokens = semantic_tokens(source);
        assert!(tokens.iter().any(|tok| tok.token_type == TYPE_PUNCTUATION));
    }

    #[test]
    fn marks_string_and_number_literals() {
        let source = "[ x := 42. y := \"ok\" ]";
        let tokens = semantic_tokens(source);
        assert!(
            tokens
                .iter()
                .any(|tok| tok.token_type == TYPE_LITERAL_NUMBER)
        );
        assert!(
            tokens
                .iter()
                .any(|tok| tok.token_type == TYPE_LITERAL_STRING)
        );
    }

    #[test]
    fn marks_block_locals() {
        let source = "[ x := 1. x ]";
        let tokens = semantic_tokens(source);
        let local_count = tokens
            .iter()
            .filter(|tok| tok.token_type == TYPE_LOCAL)
            .count();
        assert!(local_count >= 2);
    }

    #[test]
    fn marks_object_method_locals_from_slot_decls() {
        let source = "{ + rhs = { dst := rhs. dst toString } }";
        let tokens = semantic_tokens(source);
        let local_count = tokens
            .iter()
            .filter(|tok| tok.token_type == TYPE_LOCAL)
            .count();
        assert!(local_count >= 1);
    }
}
