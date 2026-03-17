use crate::asm::instrs_to_string;
use crate::ast::BoundProg;
use crate::backend::Emitter;
use crate::frontend::Resolver;
use crate::middle_end::Lowerer;
use crate::parser::ProgParser;
use crate::ssa::Program;
use crate::txt::FileInfo;

/// compiler pipeline
pub fn compile(s: &str) -> Result<String, String> {
    let (resolver, resolved_ast) = frontend(s)?;
    let (lowerer, ssa) = middle_end(resolver, resolved_ast)?;
    let asm = backend(lowerer, ssa);
    Ok(asm)
}

/// Frontend, parsing and validation
pub fn frontend(s: &str) -> Result<(Resolver, BoundProg), String> {
    let file_info = FileInfo::new(s);
    let raw_ast =
        ProgParser::new().parse(s).map_err(|e| format!("Error parsing program: {}", e))?;
    let mut resolver = Resolver::new();
    let resolved_ast = resolver
        .resolve_prog(raw_ast)
        .map_err(|e| format!("Error resolving ast: {}", file_info.report_error(e)))?;
    Ok((resolver, resolved_ast))
}

/// Middle-end, lambda lifting and SSA construction
pub fn middle_end(
    resolver: Resolver, resolved_ast: BoundProg,
) -> Result<(Lowerer, Program), String> {
    let mut lowerer = Lowerer::from(resolver);
    let ssa = lowerer.lower_prog(resolved_ast);
    Ok((lowerer, ssa))
}

/// Backend, code generation
pub fn backend(lowerer: Lowerer, ssa: Program) -> String {
    let mut emitter = Emitter::from(lowerer);
    emitter.emit_prog(&ssa);
    let asm = emitter.to_asm();
    let txt = instrs_to_string(&asm);
    txt
}
