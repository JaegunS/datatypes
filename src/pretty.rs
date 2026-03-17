use std::fmt::{self, Debug, Display};

/* ------------------------------- Combinators ------------------------------ */

struct Indent<'a, T: ?Sized>(usize, &'a T);
impl<'a, T: ?Sized> Indent<'a, T> {
    fn inner(&self) -> (usize, &'a T) {
        (self.0, self.1)
    }
}

struct Separated<'a, T, Iter>(&'a Iter, &'static str)
where
    Iter: Iterator<Item = T> + Clone;

impl<T: Display, Iter: Iterator<Item = T> + Clone> Display for Separated<'_, T, Iter> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0.clone().map(|t| t.to_string()).collect::<Vec<_>>().join(self.1))
    }
}

struct Comma<'a, T, Iter>(&'a Iter)
where
    Iter: Iterator<Item = T> + Clone;

impl<T: Display, Iter: Iterator<Item = T> + Clone> Display for Comma<'_, T, Iter> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", Separated(self.0, ", "))
    }
}

struct LineBreaks<'a, T, Iter>(&'a Iter)
where
    Iter: Iterator<Item = T> + Clone;

impl<T: Display, Iter: Iterator<Item = T> + Clone> Display for LineBreaks<'_, T, Iter> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for t in self.0.clone() {
            write!(f, "{}", t)?;
            write!(f, "\n")?;
        }
        Ok(())
    }
}

/* ----------------------------- Implementations ---------------------------- */

/// Pretty ugly printing of the (Resolved) AST
mod impl_ast {
    use super::*;
    use crate::ast::*;

    impl<Var: Display, Fun: Display> Display for Prog<Var, Fun> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            let Prog { externs, name, param: (param, _), body, loc: _ } = self;
            write!(f, "{}def {}({}): {}", LineBreaks(&externs.iter()), name, param, body)
        }
    }

    impl<Var: Display, Fun: Display> Display for ExtDecl<Var, Fun> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(f, "extern {}({}) and", self.name, Comma(&self.params.iter().map(|(p, _)| p)))
        }
    }

    impl<Var: Display, Fun: Display> Display for Expr<Var, Fun> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                Expr::Num(n, _) => write!(f, "{}", n),
                Expr::Bool(b, _) => write!(f, "{}", b),
                Expr::Var(v, _) => write!(f, "{}", v),
                Expr::Prim { prim, args, loc: _ } => match prim {
                    Prim::Add1 | Prim::Sub1 | Prim::IsType(_) | Prim::NewArray | Prim::Length => {
                        write!(f, "{}({})", prim, &args[0])
                    }
                    Prim::Add
                    | Prim::Sub
                    | Prim::Mul
                    | Prim::Not
                    | Prim::And
                    | Prim::Or
                    | Prim::Lt
                    | Prim::Le
                    | Prim::Gt
                    | Prim::Ge
                    | Prim::Eq
                    | Prim::Neq => write!(f, "({} {} {})", &args[0], prim, &args[1]),
                    Prim::MakeArray => {
                        write!(f, "[{}]", Comma(&args.into_iter()))
                    }
                    Prim::ArrayGet => {
                        write!(f, "{}[{}]", &args[0], &args[1])
                    }
                    Prim::ArraySet => {
                        write!(f, "{}[{}] := {}", &args[0], &args[1], &args[2])
                    }
                },
                Expr::Let { bindings, body, loc: _ } => {
                    write!(f, "let {} in {}", Comma(&bindings.iter()), body)
                }
                Expr::If { cond, thn, els, loc: _ } => {
                    write!(f, "if {}: {} else: {}", cond, thn, els)
                }
                Expr::FunDefs { decls, body, loc: _ } => {
                    write!(f, "{} in {}", Separated(&decls.iter(), " and "), body)
                }
                Expr::Call { fun, args, loc: _ } => {
                    write!(f, "{}({})", fun, Comma(&args.iter()))
                }
            }
        }
    }

    impl<Var: Display, Fun: Display> Display for Binding<Var, Fun> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(f, "{} = {}", self.var.0, self.expr)
        }
    }

    impl<Var: Display, Fun: Display> Display for FunDecl<Var, Fun> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(
                f,
                "def {} ({}): {}",
                self.name,
                Comma(&self.params.iter().map(|(p, _)| p)),
                self.body
            )
        }
    }

    impl Debug for Prim {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                Prim::Add => write!(f, "add"),
                Prim::Sub => write!(f, "sub"),
                Prim::Mul => write!(f, "mul"),
                Prim::Not => write!(f, "not"),
                Prim::And => write!(f, "and"),
                Prim::Or => write!(f, "or"),
                Prim::Lt => write!(f, "lt"),
                Prim::Le => write!(f, "le"),
                Prim::Gt => write!(f, "gt"),
                Prim::Ge => write!(f, "ge"),
                Prim::Eq => write!(f, "eq"),
                Prim::Neq => write!(f, "neq"),
                Prim::Add1
                | Prim::Sub1
                | Prim::IsType(_)
                | Prim::NewArray
                | Prim::MakeArray
                | Prim::ArrayGet
                | Prim::ArraySet
                | Prim::Length => Display::fmt(self, f),
            }
        }
    }

    impl Display for Prim {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                Prim::Add1 => write!(f, "add1"),
                Prim::Sub1 => write!(f, "sub1"),
                Prim::Not => write!(f, "!"),
                Prim::Add => write!(f, "+"),
                Prim::Sub => write!(f, "-"),
                Prim::Mul => write!(f, "*"),
                Prim::And => write!(f, "&&"),
                Prim::Or => write!(f, "||"),
                Prim::Lt => write!(f, "<"),
                Prim::Le => write!(f, "<="),
                Prim::Gt => write!(f, ">"),
                Prim::Ge => write!(f, ">="),
                Prim::Eq => write!(f, "=="),
                Prim::Neq => write!(f, "!="),
                Prim::IsType(ty) => write!(f, "is{}", ty),
                Prim::NewArray => write!(f, "newArray"),
                Prim::MakeArray => write!(f, "mkArray"),
                Prim::ArrayGet => write!(f, "arrayGet"),
                Prim::ArraySet => write!(f, "arraySet"),
                Prim::Length => write!(f, "length"),
            }
        }
    }
}

mod impl_ssa {
    use super::*;
    use crate::ssa::*;

    impl Display for Program {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            let Program { externs, funs, blocks } = self;
            write!(f, "{}", LineBreaks(&externs.iter()))?;
            write!(f, "{}", LineBreaks(&funs.iter()))?;
            write!(f, "{}", LineBreaks(&blocks.iter().map(|b| Indent(0, b))))?;
            Ok(())
        }
    }

    impl Display for Extern {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            let Extern { name, params } = self;
            write!(f, "extern {}({})", name, Comma(&params.iter()))
        }
    }

    impl Display for FunBlock {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            let FunBlock { name, params, body } = self;
            write!(f, "fun {}({}):\n", name, Comma(&params.iter()))?;
            write!(f, "  br {}", body)
        }
    }

    impl Display for Indent<'_, BasicBlock> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            let (indent, BasicBlock { label, params, body }) = self.inner();
            write!(f, "{}", "  ".repeat(indent))?;
            write!(f, "block {}({}):\n{}", label, Comma(&params.iter()), Indent(indent + 1, body))
        }
    }

    impl Display for Indent<'_, BlockBody> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            let (indent, body) = self.inner();
            match body {
                BlockBody::Terminator(terminator) => {
                    write!(f, "{}", "  ".repeat(indent))?;
                    write!(f, "{}", terminator)
                }
                BlockBody::Operation { dest, op, next } => {
                    write!(f, "{}", "  ".repeat(indent))?;
                    write!(f, "{} = {}\n{}", dest, op, Indent(indent, next.as_ref()))
                }
                BlockBody::SubBlocks { blocks, next } => {
                    write!(f, "{}", LineBreaks(&blocks.iter().map(|b| Indent(indent, b))))?;
                    write!(f, "{}", Indent(indent, next.as_ref()))
                }
                BlockBody::AssertType { ty, arg: of, next } => {
                    write!(f, "{}", "  ".repeat(indent))?;
                    write!(f, "assert{}({})\n{}", ty, of, Indent(indent, next.as_ref()))
                }
                BlockBody::AssertLength { len, next } => {
                    write!(f, "{}", "  ".repeat(indent))?;
                    write!(f, "assertLength({})\n{}", len, Indent(indent, next.as_ref()))
                }
                BlockBody::AssertInBounds { bound, arg: of, next } => {
                    write!(f, "{}", "  ".repeat(indent))?;
                    write!(
                        f,
                        "assertInBounds({}, {})\n{}",
                        bound,
                        of,
                        Indent(indent, next.as_ref())
                    )
                }
                BlockBody::Store { addr, offset: off, val, next } => {
                    write!(f, "{}", "  ".repeat(indent))?;
                    write!(
                        f,
                        "store({}, {}, {})\n{}",
                        addr,
                        off,
                        val,
                        Indent(indent, next.as_ref())
                    )
                }
            }
        }
    }

    impl Display for Terminator {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                Terminator::Return(imm) => write!(f, "ret {}", imm),
                Terminator::Branch(branch) => write!(f, "br {}", branch),
                Terminator::ConditionalBranch { cond, thn, els } => {
                    write!(f, "cbr {} {} {}", cond, thn, els)
                }
            }
        }
    }

    impl Display for Branch {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            let Branch { target, args } = self;
            write!(f, "{}({})", target, Comma(&args.iter()))
        }
    }

    impl Display for Operation {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                Operation::Immediate(imm) => write!(f, "{}", imm),
                Operation::Prim1(prim @ Prim1::BitNot, imm) => write!(f, "{} {}", prim, imm),
                Operation::Prim1(prim, imm) => write!(f, "{} {}", imm, prim),
                Operation::Prim2(prim, imm1, imm2) => write!(f, "{} {} {}", imm1, prim, imm2),
                Operation::Call { fun, args } => write!(f, "{}({})", fun, Comma(&args.iter())),
                Operation::AllocateArray { len } => write!(f, "allocateArray({})", len),
                Operation::Load { addr, offset: off } => write!(f, "load({}, {})", addr, off),
            }
        }
    }

    impl Debug for Prim1 {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                Prim1::BitNot => write!(f, "bit_not"),
                Prim1::BitSal(n) => write!(f, "bit_sal/{}", n),
                Prim1::BitSar(n) => write!(f, "bit_sar/{}", n),
                Prim1::BitShl(n) => write!(f, "bit_shl/{}", n),
                Prim1::BitShr(n) => write!(f, "bit_shr/{}", n),
            }
        }
    }
    impl Display for Prim1 {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                Prim1::BitNot => write!(f, "~"),
                Prim1::BitSal(n) => write!(f, "<< {}", n),
                Prim1::BitSar(n) => write!(f, ">> {}", n),
                Prim1::BitShl(n) => write!(f, "<<< {}", n),
                Prim1::BitShr(n) => write!(f, ">>> {}", n),
            }
        }
    }

    impl Debug for Prim2 {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                Prim2::Add => write!(f, "add"),
                Prim2::Sub => write!(f, "sub"),
                Prim2::Mul => write!(f, "mul"),
                Prim2::BitAnd => write!(f, "bit_and"),
                Prim2::BitOr => write!(f, "bit_or"),
                Prim2::BitXor => write!(f, "bit_xor"),
                Prim2::Lt => write!(f, "lt"),
                Prim2::Le => write!(f, "le"),
                Prim2::Gt => write!(f, "gt"),
                Prim2::Ge => write!(f, "ge"),
                Prim2::Eq => write!(f, "eq"),
                Prim2::Neq => write!(f, "neq"),
            }
        }
    }

    impl Display for Prim2 {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                Prim2::Add => write!(f, "+"),
                Prim2::Sub => write!(f, "-"),
                Prim2::Mul => write!(f, "*"),
                Prim2::BitAnd => write!(f, "&"),
                Prim2::BitOr => write!(f, "|"),
                Prim2::BitXor => write!(f, "^"),
                Prim2::Lt => write!(f, "<"),
                Prim2::Le => write!(f, "<="),
                Prim2::Gt => write!(f, ">"),
                Prim2::Ge => write!(f, ">="),
                Prim2::Eq => write!(f, "=="),
                Prim2::Neq => write!(f, "!="),
            }
        }
    }

    impl Display for Immediate {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                Immediate::Const(c) => write!(f, "{}", c),
                Immediate::Var(v) => write!(f, "{}", v),
            }
        }
    }
}
