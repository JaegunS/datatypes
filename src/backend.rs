//! The backend of our compiler translates our intermediate
//! representation into assembly code, mapping intermediate
//! representation variables into concrete memory locations.

use crate::asm::*;
use crate::identifiers::*;
use crate::middle_end::Lowerer;
use crate::ssa::*;
use crate::types::*;

/*blank*/
#[derive(Clone)]
struct Env<'a> {
    next: i32,
    arena: im::HashMap<&'a VarName, i32>,
    blocks: im::HashMap<&'a BlockName, i32>,
}

impl<'a> Env<'a> {
    fn new() -> Self {
        Env { next: 1, arena: im::HashMap::new(), blocks: im::HashMap::new() }
    }
    fn allocate(&mut self, x: &'a VarName) -> i32 {
        let loc = self.next;
        self.arena.insert(x, loc);
        self.next += 1;
        loc
    }
    fn lookup(&self, x: &'a VarName) -> i32 {
        self.arena.get(x).copied().expect("variable not allocated")
    }
}

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
        /*todo:finish implementing emit_prog*/
        let Program { externs, funs, blocks } = prog;
        let mut env = Env::new();

        // emit text section
        self.emit(Instr::Section(".text".to_string()));
        self.emit(Instr::Global("entry".to_string()));
        // emit the externs
        for ext in externs.iter() {
            self.emit(Instr::Extern(ext.name.hint().to_owned()));
        }

        // emit the functions
        for fun in funs.iter() {
            self.emit_fun_block(fun, &env);
        }

        // finally, emit the blocks
        // first register all the block alignments
        for BasicBlock { label, .. } in blocks {
            env.blocks.insert(label, env.next);
        }
        // then emit the sub-blocks, each with a cloned environment
        for BasicBlock { label, params, body } in blocks {
            let mut env = env.clone();
            self.emit(Instr::Label(label.to_string()));
            for param in params {
                env.allocate(param);
            }
            self.emit_block_body(body, &mut env);
        }
        /*end*/
    }

    /*blank*/
    /// The System-V calling convention uses the following registers for the first 6 arguments.
    const REGS: [Reg; 6] = [Reg::Rdi, Reg::Rsi, Reg::Rdx, Reg::Rcx, Reg::R8, Reg::R9];

    /// FunBlocks move the arguments from their designated place in
    /// the Sys V calling convention to negative offsets from rsp.
    fn emit_fun_block<'a>(
        &mut self, FunBlock { name, params, body }: &'a FunBlock, _env: &Env<'a>,
    ) {
        self.emit(Instr::Label(name.to_string()));
        for (i, (reg, _param)) in Self::REGS.iter().zip(params.iter()).enumerate() {
            self.emit(store_mem((i + 1) as i32, *reg));
        }
        for (i, _param) in params.iter().enumerate().skip(Self::REGS.len()) {
            let j = i + 1;
            let src: i32 = -1 * ((j - Self::REGS.len()) as i32);
            self.emit(load_mem(Reg::Rax, src));
            self.emit(store_mem(j as i32, Reg::Rax));
        }
        self.emit(Instr::Jmp(JmpArgs::Label(body.target.to_string())));
    }

    fn emit_block_body<'a>(&mut self, b: &'a BlockBody, env: &mut Env<'a>) {
        match b {
            BlockBody::Terminator(terminator) => {
                self.emit_terminator(terminator, env);
            }
            BlockBody::Operation { dest, op, next } => {
                self.emit_operation(dest, op, env);
                self.emit_block_body(next, env);
            }
            BlockBody::SubBlocks { blocks, next } => {
                // register all the block alignments first
                for BasicBlock { label, .. } in blocks {
                    env.blocks.insert(label, env.next);
                }
                // then emit the body with a cloned environment
                self.emit_block_body(next, &mut env.clone());
                // and finally, emit the sub-blocks, each with a cloned environment
                for BasicBlock { label, params, body } in blocks {
                    let mut env = env.clone();
                    self.emit(Instr::Label(label.to_string()));
                    for param in params {
                        env.allocate(param);
                    }
                    self.emit_block_body(body, &mut env);
                }
            }
        }
    }

    fn emit_terminator<'a>(&mut self, t: &'a Terminator, env: &Env<'a>) {
        match t {
            Terminator::Return(imm) => {
                self.emit_imm_reg(imm, Reg::Rax, env);
                self.emit(Instr::Ret);
            }
            Terminator::Branch(branch) => {
                self.emit_branch(branch, env);
            }
            Terminator::ConditionalBranch { cond, thn, els } => {
                self.emit_imm_reg(cond, Reg::Rax, env);
                self.emit(Instr::Cmp(BinArgs::ToReg(Reg::Rax, Arg32::Signed(0))));
                self.emit(Instr::JCC(ConditionCode::NE, thn.to_string()));
                self.emit(Instr::Jmp(JmpArgs::Label(els.to_string())));
            }
        }
    }

    fn emit_branch<'a>(&mut self, Branch { target, args }: &'a Branch, env: &Env<'a>) {
        // lookup the base offset for the target's arguments
        let base = env.blocks[target];

        // store arguments in consecutive offsets from the target's base
        for (i, arg) in args.iter().enumerate() {
            // using Rax as a temp register
            self.emit_imm_reg(arg, Reg::Rax, env);
            self.emit(store_mem(base + i as i32, Reg::Rax));
        }
        // finally, jump to the target
        self.emit(Instr::Jmp(JmpArgs::Label(target.to_string())));
    }

    fn emit_operation<'a>(&mut self, dest: &'a VarName, op: &'a Operation, env: &mut Env<'a>) {
        // dst is the position of the destination variable on the stack;
        // -8 * dst is its memory offset
        // remember to write the result back to the destination at the end of the function
        match op {
            Operation::Immediate(imm) => {
                self.emit_imm_reg(imm, Reg::Rax, env);
            }
            Operation::Prim1(op, imm) => {
                self.emit_imm_reg(imm, Reg::Rax, env);
                match op {
                    Prim1::BitNot => {
                        self.emit(Instr::Mov(MovArgs::ToReg(Reg::R10, Arg64::Signed(-1))));
                        self.emit(Instr::Xor(BinArgs::ToReg(Reg::Rax, Arg32::Reg(Reg::R10))));
                    }
                    Prim1::IntToBool => {
                        // if reg is not zero, make it 1, otherwise make it 0
                        self.emit(Instr::Cmp(BinArgs::ToReg(Reg::Rax, Arg32::Signed(0))));
                        self.emit(Instr::Mov(MovArgs::ToReg(Reg::Rax, Arg64::Signed(0))));
                        self.emit(Instr::SetCC(ConditionCode::NE, Reg8::Al));
                    }
                }
            }
            Operation::Prim2(op, imm1, imm2) => {
                self.emit_imm_reg(imm1, Reg::Rax, env);
                self.emit_imm_reg(imm2, Reg::R10, env);
                let ba = BinArgs::ToReg(Reg::Rax, Arg32::Reg(Reg::R10));
                match op {
                    Prim2::Add => self.emit(Instr::Add(ba)),
                    Prim2::Sub => self.emit(Instr::Sub(ba)),
                    Prim2::Mul => self.emit(Instr::IMul(ba)),
                    Prim2::BitAnd => self.emit(Instr::And(ba)),
                    Prim2::BitOr => self.emit(Instr::Or(ba)),
                    Prim2::BitXor => self.emit(Instr::Xor(ba)),
                    Prim2::Lt => self.emit_cc(ConditionCode::L, ba),
                    Prim2::Gt => self.emit_cc(ConditionCode::G, ba),
                    Prim2::Le => self.emit_cc(ConditionCode::LE, ba),
                    Prim2::Ge => self.emit_cc(ConditionCode::GE, ba),
                    Prim2::Eq => self.emit_cc(ConditionCode::E, ba),
                    Prim2::Neq => self.emit_cc(ConditionCode::NE, ba),
                }
            }
            Operation::Call { fun, args } => {
                // System-V calling convention
                // 1. Store the first 6 arguments in registers
                for (reg, arg) in Self::REGS.iter().zip(args.iter()) {
                    self.emit_imm_reg(arg, *reg, env);
                }
                // 2. calculate where the return address should be stored:
                //    - after all of the currently allocated locals (env.next)
                //    - after all of the stack-passed arguments (arg.len() - REGS.len())
                //    - at an *odd* multiple of 8 from the previous rsp
                let num_stack_args = args.len().saturating_sub(Self::REGS.len()) as i32;
                let frame_size = {
                    let mut f = env.next + num_stack_args;
                    // comment out the following line for mutation testing
                    f += if f % 2 == 1 { 0 } else { 1 };
                    f
                };

                if frame_size % 2 == 0 {
                    panic!("We were about to misalign the stack! in call {}", op);
                }

                // store the remaining arguments in the stack
                for (i, arg) in args.iter().skip(Self::REGS.len()).enumerate() {
                    // using Rax as a temp register
                    self.emit_imm_reg(arg, Reg::Rax, env);
                    self.emit(store_mem(frame_size - i as i32, Reg::Rax));
                }

                // move the stack pointer to allocate the next stack frame
                self.emit(Instr::Sub(BinArgs::ToReg(Reg::Rsp, Arg32::Signed(8 * frame_size))));
                // call the function
                self.emit(Instr::Call(JmpArgs::Label(fun.to_string())));
                // move the stack pointer back to the previous stack frame
                self.emit(Instr::Add(BinArgs::ToReg(Reg::Rsp, Arg32::Signed(8 * frame_size))));
            }
        }

        let dst = env.allocate(dest);
        // write the return value back to the destination
        // self.emit(Instr::Comment(format!("store {}", dest)));
        self.emit(store_mem(dst, Reg::Rax))
    }

    fn emit_cc(&mut self, cc: ConditionCode, ba: BinArgs) {
        self.emit(Instr::Cmp(ba));
        self.emit(Instr::Mov(MovArgs::ToReg(Reg::Rax, Arg64::Signed(0))));
        self.emit(Instr::SetCC(cc, Reg8::Al))
    }

    fn emit_imm_reg<'a>(&mut self, imm: &'a Immediate, reg: Reg, env: &Env<'a>) {
        match imm {
            Immediate::Var(v) => {
                let src = env.lookup(v);
                // self.emit(Instr::Comment(format!("load {}", v)));
                self.emit(load_mem(reg, src))
            }
            Immediate::Const(i) => {
                self.emit(load_signed(reg, *i));
            }
        }
    }
    /*end*/
}

/*blank*/
/// Put the value of a signed constant into a register.
fn load_signed(reg: Reg, val: i64) -> Instr {
    Instr::Mov(MovArgs::ToReg(reg, Arg64::Signed(val)))
}

/// Put the value of a memory reference into a register.
fn load_mem(reg: Reg, src: i32) -> Instr {
    Instr::Mov(MovArgs::ToReg(reg, Arg64::Mem(MemRef { reg: Reg::Rsp, offset: -8 * src })))
}

/// Flush the value of a register into a memory reference.
fn store_mem(dst: i32, reg: Reg) -> Instr {
    Instr::Mov(MovArgs::ToMem(MemRef { reg: Reg::Rsp, offset: -8 * dst }, Reg32::Reg(reg)))
}
/*end*/
