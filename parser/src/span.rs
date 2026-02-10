/// Source location and span tracking.
///
/// Every token and AST node carries a [`Span`] that records exactly where
/// it appeared in the source text — byte offset, line, and column for both
/// the start and end positions.

/// A single position in source text.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Pos {
    /// Byte offset from the start of the input (0-based).
    pub offset: usize,
    /// Line number (1-based).
    pub line: usize,
    /// Column number (1-based, in bytes — not grapheme clusters).
    pub column: usize,
}

impl Pos {
    pub const fn new(offset: usize, line: usize, column: usize) -> Self {
        Self {
            offset,
            line,
            column,
        }
    }

    /// The very beginning of a source text.
    pub const fn origin() -> Self {
        Self {
            offset: 0,
            line: 1,
            column: 1,
        }
    }
}

impl std::fmt::Display for Pos {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}", self.line, self.column)
    }
}

/// A contiguous region of source text.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Span {
    pub start: Pos,
    pub end: Pos,
}

impl Span {
    pub const fn new(start: Pos, end: Pos) -> Self {
        Self { start, end }
    }

    /// Create a zero-width span at a single position.
    pub const fn point(pos: Pos) -> Self {
        Self {
            start: pos,
            end: pos,
        }
    }

    /// Merge two spans into one that covers both.
    pub fn merge(self, other: Span) -> Span {
        let start = if self.start.offset <= other.start.offset {
            self.start
        } else {
            other.start
        };
        let end = if self.end.offset >= other.end.offset {
            self.end
        } else {
            other.end
        };
        Span { start, end }
    }
}

impl std::fmt::Display for Span {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}-{}", self.start, self.end)
    }
}
