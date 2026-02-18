use tower_lsp::lsp_types::Position;

pub fn byte_offset_to_position(source: &str, offset: usize) -> Position {
    let clamped = clamp_to_char_boundary(source, offset.min(source.len()));

    let mut line: u32 = 0;
    let mut line_start = 0;

    for (idx, ch) in source.char_indices() {
        if idx >= clamped {
            break;
        }
        if ch == '\n' {
            line += 1;
            line_start = idx + ch.len_utf8();
        }
    }

    let character = source[line_start..clamped].encode_utf16().count() as u32;
    Position { line, character }
}

pub fn lsp_position_to_byte_offset(
    source: &str,
    pos: Position,
) -> Option<usize> {
    let mut line_start = 0usize;
    let mut current_line = 0u32;

    if pos.line > 0 {
        for (idx, ch) in source.char_indices() {
            if ch == '\n' {
                current_line += 1;
                line_start = idx + ch.len_utf8();
                if current_line == pos.line {
                    break;
                }
            }
        }
        if current_line != pos.line {
            return None;
        }
    }

    let line_end = source[line_start..]
        .find('\n')
        .map(|rel| line_start + rel)
        .unwrap_or(source.len());
    let line_text = &source[line_start..line_end];

    let mut utf16_col = 0u32;
    for (rel_idx, ch) in line_text.char_indices() {
        if utf16_col == pos.character {
            return Some(line_start + rel_idx);
        }
        utf16_col += ch.len_utf16() as u32;
        if utf16_col > pos.character {
            return None;
        }
    }

    if utf16_col == pos.character {
        return Some(line_end);
    }

    None
}

fn clamp_to_char_boundary(source: &str, mut offset: usize) -> usize {
    while offset > 0 && !source.is_char_boundary(offset) {
        offset -= 1;
    }
    offset
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn maps_ascii_offset() {
        let source = "abc\ndef";
        assert_eq!(byte_offset_to_position(source, 5), Position::new(1, 1));
    }

    #[test]
    fn maps_utf16_column() {
        let source = "a🎉b";
        let pos = byte_offset_to_position(source, "a🎉".len());
        assert_eq!(pos, Position::new(0, 3));
    }

    #[test]
    fn clamps_non_boundary_offsets() {
        let source = "a🎉b";
        let mid = 2;
        let pos = byte_offset_to_position(source, mid);
        assert_eq!(pos, Position::new(0, 1));
    }

    #[test]
    fn maps_position_back_to_ascii_offset() {
        let source = "abc\ndef";
        let off = lsp_position_to_byte_offset(source, Position::new(1, 2));
        assert_eq!(off, Some(6));
    }

    #[test]
    fn maps_position_back_to_utf16_offset() {
        let source = "a🎉b";
        let off = lsp_position_to_byte_offset(source, Position::new(0, 3));
        assert_eq!(off, Some("a🎉".len()));
    }

    #[test]
    fn rejects_invalid_mid_surrogate_position() {
        let source = "a🎉b";
        let off = lsp_position_to_byte_offset(source, Position::new(0, 2));
        assert_eq!(off, None);
    }
}
