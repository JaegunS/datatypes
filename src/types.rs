#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Type {
    Int,
    Bool,
    Array,
}

mod impls {
    use super::*;
    use std::fmt;

    impl Type {
        pub fn tag(self) -> i64 {
            match self {
                Type::Int => 0b0,
                Type::Bool => 0b01,
                Type::Array => 0b11,
            }
        }
        pub fn mask(self) -> i64 {
            match self {
                Type::Int => 0b01,
                Type::Bool | Type::Array => 0b11,
            }
        }
        pub fn mask_length(self) -> u8 {
            match self {
                Type::Int => 1,
                Type::Bool | Type::Array => 2,
            }
        }
    }

    impl fmt::Debug for Type {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                Self::Int => write!(f, "Integer"),
                Self::Bool => write!(f, "Boolean"),
                Self::Array => write!(f, "Array"),
            }
        }
    }

    impl fmt::Display for Type {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                Self::Int => write!(f, "Int"),
                Self::Bool => write!(f, "Bool"),
                Self::Array => write!(f, "Array"),
            }
        }
    }
}
