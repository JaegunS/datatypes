use crate::frontend::CompileErr;
use crate::span::{Span2, SrcLoc};
#[derive(Clone, Debug)]
pub struct FileInfo {
    newlines: Vec<usize>,
    len: usize,
}

impl FileInfo {
    pub fn new(s: &str) -> Self {
        FileInfo {
            newlines: s.char_indices().filter(|(_i, c)| *c == '\n').map(|(i, _c)| i).collect(),
            len: s.len(),
        }
    }

    pub fn span1_to_span2(&self, offsets: SrcLoc) -> Span2 {
        let mut v = vec![0];
        v.extend(self.newlines.iter().map(|ix| ix + 1));
        v.push(self.len);

        let (start_line, start_col) = Self::offset_to_line_col(&v, offsets.start_ix);
        let (end_line, end_col) = Self::offset_to_line_col(&v, offsets.end_ix - 1);
        Span2 { start_line, start_col, end_line, end_col: end_col + 1 }
    }

    fn offset_to_line_col(newlines: &[usize], offset: usize) -> (usize, usize) {
        let mut win = newlines.windows(2).enumerate();
        while let Some((line, &[start, end])) = win.next() {
            if start <= offset && offset < end {
                return (line + 1, offset - start);
            }
        }
        panic!("internal error: offset_to_line_col. Send this to the professor");
    }

    pub fn report_error(&self, err: CompileErr) -> String {
        use CompileErr::*;
        match err {
            UnboundVariable(v, span1) => {
                format!("variable \"{}\" unbound: {}", v, self.span1_to_span2(span1))
            }
            DuplicateVariable(v, span1) => format!(
                "variable \"{}\" defined twice in let-expression: {}",
                v,
                self.span1_to_span2(span1)
            ),
            UnboundFunction(f, span1) => {
                format!("function \"{}\" undefined: {}", f, self.span1_to_span2(span1))
            }
            DuplicateFunction(f, span1) => format!(
                "multiple defined functions named \"{}\": {}",
                f,
                self.span1_to_span2(span1)
            ),
            DuplicateParameter(p, span1) => {
                format!("multiple parameters named \"{}\": {}", p, self.span1_to_span2(span1))
            }
            ArityMismatch { name, expected, found, loc } => format!(
                "function \"{}\" of arity {} called with {} arguments: {}",
                name,
                expected,
                found,
                self.span1_to_span2(loc)
            ),
            IntegerOverflow(i, loc) => {
                format!("integer {} overflow: {}", i, self.span1_to_span2(loc))
            }
        }
    }
}
