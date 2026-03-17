use crate::identifiers::*;
use crate::types::*;

#[derive(Clone, Debug)]
pub struct Program {
    pub externs: Vec<Extern>,
    pub funs: Vec<FunBlock>,
    pub blocks: Vec<BasicBlock>,
}

#[derive(Clone, Debug)]
pub struct Extern {
    pub name: FunName,
    pub params: Vec<VarName>,
}

#[derive(Clone, Debug)]
pub struct FunBlock {
    pub name: FunName,
    pub params: Vec<VarName>,
    pub body: Branch,
}

#[derive(Clone, Debug)]
pub struct BasicBlock {
    pub label: BlockName,
    pub params: Vec<VarName>,
    pub body: BlockBody,
}

#[derive(Clone, Debug)]
pub enum BlockBody {
    Terminator(Terminator),
    Operation {
        dest: VarName,
        op: Operation,
        next: Box<BlockBody>,
    },
    SubBlocks {
        blocks: Vec<BasicBlock>,
        next: Box<BlockBody>,
    },
    /// arg: tagged
    AssertType {
        ty: Type,
        arg: Immediate,
        next: Box<BlockBody>,
    },
    /// len: untagged
    AssertLength {
        len: Immediate,
        next: Box<BlockBody>,
    },
    /// bound: untagged, arg: untagged
    AssertInBounds {
        bound: Immediate,
        arg: Immediate,
        next: Box<BlockBody>,
    },
    /// addr: untagged, offset: untagged, val: either
    Store {
        addr: Immediate,
        offset: Immediate,
        val: Immediate,
        next: Box<BlockBody>,
    },
}

#[derive(Clone, Debug)]
pub enum Terminator {
    Return(Immediate),
    Branch(Branch),
    ConditionalBranch { cond: Immediate, thn: BlockName, els: BlockName },
}

#[derive(Clone, Debug)]
pub struct Branch {
    pub target: BlockName,
    pub args: Vec<Immediate>,
}

#[derive(Clone, Debug)]
pub enum Operation {
    Immediate(Immediate),
    Prim1(Prim1, Immediate),
    Prim2(Prim2, Immediate, Immediate),
    Call {
        fun: FunName,
        args: Vec<Immediate>,
    },
    /// len: untagged
    AllocateArray {
        len: Immediate,
    },
    /// addr: untagged, offset: untagged
    Load {
        addr: Immediate,
        offset: Immediate,
    },
}

#[derive(Clone, PartialEq, Eq)]
pub enum Prim1 {
    BitNot,
    // shift
    BitSal(u8),
    BitSar(u8),
    BitShl(u8),
    BitShr(u8),
}

#[derive(Clone, PartialEq, Eq)]
pub enum Prim2 {
    // arithmetic
    Add,
    Sub,
    Mul,
    // logical
    BitAnd,
    BitOr,
    BitXor,
    // comparison
    Lt,
    Le,
    Gt,
    Ge,
    Eq,
    Neq,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Immediate {
    Const(i64),
    Var(VarName),
}
