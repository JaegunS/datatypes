//! The backend of our compiler translates our intermediate
//! representation into assembly code, mapping intermediate
//! representation variables into concrete memory locations.

use crate::asm::*;
use crate::identifiers::*;
use crate::middle_end::Lowerer;
use crate::ssa::*;
use crate::types::*;

pub struct Emitter {
    // the output buffer for the sequence of instructions we are generating
    instrs: Vec<Instr>,
}

impl From<Lowerer> for Emitter {
    fn from(Lowerer { .. }: Lowerer) -> Self {
        Emitter { instrs: Vec::new() }
    }
}

/// Example runtime error codes.
#[repr(u64)]
pub enum SnakeErr {
    ArithmeticOverflow = 0,
    ExpectedNum = 1,
    ExpectedBool = 2,
    ExpectedArray = 3,
    NegativeLength = 4,
    IndexOutOfBounds = 5,
}

impl Emitter {
    pub fn to_asm(self) -> Vec<Instr> {
        self.instrs
    }

    fn emit(&mut self, instr: Instr) {
        self.instrs.push(instr);
    }

    pub fn emit_prog(&mut self, prog: &Program) {
        let Program { externs, funs, blocks } = prog;
        // emit text section
        self.emit(Instr::Section(".text".to_string()));
        self.emit(Instr::Global("entry".to_string()));

        // emit the system externs
        self.emit(Instr::Extern(format!("snake_error")));
        self.emit(Instr::Extern(format!("snake_new_array")));

        todo!("finish implementing emit_prog")
    }
}
