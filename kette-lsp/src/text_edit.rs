use tower_lsp::lsp_types::TextDocumentContentChangeEvent;

use crate::position::lsp_position_to_byte_offset;

pub fn apply_content_changes(
    source: &mut String,
    changes: &[TextDocumentContentChangeEvent],
) -> Result<(), String> {
    for change in changes {
        match &change.range {
            Some(range) => {
                let start = lsp_position_to_byte_offset(source, range.start)
                    .ok_or_else(|| {
                        format!(
                            "invalid change start position {}:{}",
                            range.start.line, range.start.character
                        )
                    })?;
                let end = lsp_position_to_byte_offset(source, range.end)
                    .ok_or_else(|| {
                        format!(
                            "invalid change end position {}:{}",
                            range.end.line, range.end.character
                        )
                    })?;

                if start > end {
                    return Err("change start is after end".to_string());
                }

                source.replace_range(start..end, &change.text);
            }
            None => {
                *source = change.text.clone();
            }
        }
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use tower_lsp::lsp_types::{
        Position, Range, TextDocumentContentChangeEvent,
    };

    use super::*;

    #[test]
    fn applies_full_document_replace() {
        let mut source = "x := 1".to_string();
        let change = TextDocumentContentChangeEvent {
            range: None,
            range_length: None,
            text: "x := 2".to_string(),
        };

        apply_content_changes(&mut source, &[change]).expect("apply changes");
        assert_eq!(source, "x := 2");
    }

    #[test]
    fn applies_incremental_ascii_change() {
        let mut source = "x := 1\ny := 2".to_string();
        let change = TextDocumentContentChangeEvent {
            range: Some(Range::new(Position::new(1, 5), Position::new(1, 6))),
            range_length: None,
            text: "9".to_string(),
        };

        apply_content_changes(&mut source, &[change]).expect("apply changes");
        assert_eq!(source, "x := 1\ny := 9");
    }

    #[test]
    fn applies_incremental_unicode_change_utf16_columns() {
        let mut source = "name := \"a🎉b\"".to_string();
        let change = TextDocumentContentChangeEvent {
            range: Some(Range::new(Position::new(0, 10), Position::new(0, 12))),
            range_length: None,
            text: "z".to_string(),
        };

        apply_content_changes(&mut source, &[change]).expect("apply changes");
        assert_eq!(source, "name := \"azb\"");
    }

    #[test]
    fn applies_multiple_incremental_changes_in_order() {
        let mut source = "foo bar".to_string();
        let changes = [
            TextDocumentContentChangeEvent {
                range: Some(Range::new(
                    Position::new(0, 0),
                    Position::new(0, 3),
                )),
                range_length: None,
                text: "baz".to_string(),
            },
            TextDocumentContentChangeEvent {
                range: Some(Range::new(
                    Position::new(0, 4),
                    Position::new(0, 7),
                )),
                range_length: None,
                text: "qux".to_string(),
            },
        ];

        apply_content_changes(&mut source, &changes).expect("apply changes");
        assert_eq!(source, "baz qux");
    }
}
