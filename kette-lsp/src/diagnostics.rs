use parser::ParseError;
#[cfg(test)]
use parser::{Lexer, Parser};
use tower_lsp::lsp_types::{
    Diagnostic, DiagnosticSeverity, NumberOrString, Range,
};

use crate::position::byte_offset_to_position;

const SOURCE_NAME: &str = "kette-parser";

#[cfg(test)]
pub fn parse_diagnostics(source: &str) -> Vec<Diagnostic> {
    let lexer = Lexer::from_str(source);
    let parser = Parser::new(lexer);

    let errors: Vec<ParseError> = parser.filter_map(Result::err).collect();
    diagnostics_from_parse_errors(source, &errors)
}

pub fn diagnostics_from_parse_errors(
    source: &str,
    errors: &[ParseError],
) -> Vec<Diagnostic> {
    errors
        .iter()
        .map(|err| {
            let start = err.span.start.offset;
            let mut end = err.span.end.offset;
            if end < start {
                end = start;
            }

            let range = Range::new(
                byte_offset_to_position(source, start),
                byte_offset_to_position(source, end),
            );

            Diagnostic {
                range,
                severity: Some(DiagnosticSeverity::ERROR),
                code: Some(NumberOrString::String("parse-error".to_string())),
                code_description: None,
                source: Some(SOURCE_NAME.to_string()),
                message: err.message.clone(),
                related_information: None,
                tags: None,
                data: None,
            }
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn returns_no_diagnostics_for_valid_source() {
        let diags = parse_diagnostics("x := 1. x + 2");
        assert!(diags.is_empty());
    }

    #[test]
    fn returns_diagnostic_for_invalid_source() {
        let diags = parse_diagnostics("x :=");
        assert!(!diags.is_empty());
        assert!(diags[0].message.contains("unexpected end of input"));
    }
}
