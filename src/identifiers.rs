//! Define the identifiers used across the compiler.

/* ------------------------------- Identifiers ------------------------------ */

/// A `VarName` is a unique identifier for a variable.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct VarName(usize, String);
impl VarName {
    pub fn hint(&self) -> &str {
        &self.1
    }
}

/// A `FunName` is a unique identifier for a function name.
/// It can be either mangled or unmangled.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum FunName {
    /// A mangled function name that is unique globally.
    Mangled(usize, String),
    /// An unmangled function name that can be used to refer to an external
    /// function or the entry point of the program.
    Unmangled(String),
}
impl FunName {
    pub fn unmangled(hint: impl Into<String>) -> Self {
        Self::Unmangled(hint.into())
    }
    pub fn hint(&self) -> &str {
        match self {
            FunName::Mangled(_, hint) | FunName::Unmangled(hint) => hint,
        }
    }
    pub fn is_unmangled(&self) -> bool {
        match self {
            FunName::Unmangled(..) => true,
            FunName::Mangled(..) => false,
        }
    }
}

/// A `BlockName` is a unique identifier for a basic block in IR.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct BlockName(usize, String);
impl BlockName {
    pub fn hint(&self) -> &str {
        &self.1
    }
}

/* --------------------------------- Display -------------------------------- */

mod impl_display {
    use super::*;
    use std::fmt;

    impl fmt::Display for VarName {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(f, "{}%{}", self.1, self.0)
        }
    }
    impl fmt::Display for FunName {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                FunName::Mangled(idx, hint) => write!(f, "{}@{}", hint, idx),
                FunName::Unmangled(hint) => write!(f, "{}", hint),
            }
        }
    }
    impl fmt::Display for BlockName {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(f, "{}#{}", self.1, self.0)
        }
    }
}

/* -------------------------- Identifier Generator -------------------------- */

/// A `IdGen` is a generator of unique `VarName`s.
pub struct IdGen<Id> {
    count: usize,
    _marker: std::marker::PhantomData<Id>,
}

mod impl_idgen {
    use super::*;

    pub trait Identifier: Clone {
        fn new(idx: usize, hint: impl Into<String>) -> Self;
    }
    impl Identifier for VarName {
        fn new(idx: usize, hint: impl Into<String>) -> Self {
            Self(idx, hint.into())
        }
    }
    impl Identifier for FunName {
        fn new(idx: usize, hint: impl Into<String>) -> Self {
            Self::Mangled(idx, hint.into())
        }
    }
    impl Identifier for BlockName {
        fn new(idx: usize, hint: impl Into<String>) -> Self {
            Self(idx, hint.into())
        }
    }

    impl<Id: Identifier> IdGen<Id> {
        pub fn new() -> Self {
            Self { count: 0, _marker: std::marker::PhantomData }
        }
        pub fn fresh(&mut self, hint: impl Into<String>) -> Id {
            let id = Id::new(self.count, hint);
            self.count += 1;
            id
        }
    }
}
