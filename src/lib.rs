/* ----------------------------- Compiler Passes ---------------------------- */
pub mod txt;
pub mod frontend;
pub mod ast;
pub mod middle_end;
pub mod ssa;
pub mod backend;
pub mod asm;
pub mod compile;
pub mod parser;

/* -------------------------------- Utilities ------------------------------- */
pub mod identifiers;
pub mod types;
pub mod span;
pub mod pretty;
pub mod interp;
pub mod runner;
