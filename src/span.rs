//! A Span is a region of source code.

/// 1-dimensional span of source locations.
///
/// This is what the parser outputs.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SrcLoc {
    pub start_ix: usize,
    pub end_ix: usize, // exclusive
}
impl SrcLoc {
    pub fn new(start_ix: usize, end_ix: usize) -> Self {
        Self { start_ix, end_ix }
    }
}

/// 2-dimensional span of source locations.
///
/// This is what we use in error messages.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Span2 {
    pub start_line: usize,
    pub start_col: usize,
    pub end_line: usize, // inclusive
    pub end_col: usize,  // exclusive
}

impl std::fmt::Display for Span2 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Span2 { start_line, start_col, end_line, end_col } = self;
        write!(f, "{start_line}:{start_col}-{end_line}:{end_col}",)
    }
}
