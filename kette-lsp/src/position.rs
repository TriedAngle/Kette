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
}
