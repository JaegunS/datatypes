use clap::{Parser, ValueEnum};
use diamondback::{
    asm::instrs_to_string, backend::Emitter, frontend::Resolver, interp, middle_end::Lowerer,
    parser::ProgParser, runner::*, txt::FileInfo,
};
use std::path::{Path, PathBuf};

#[derive(Parser, Debug)]
#[command(about, long_about = None)]
struct Cli {
    /// File containing the input program
    input_file: String,

    /// Optional target type. Defaults to asm
    #[arg(value_enum, short, long, value_name = "target")]
    target: Option<Target>,

    /// Optional output file. For target exe, defaults to runtime/stub.exe, otherwise if not present prints to stdout
    #[arg(short, long, value_name = "output")]
    output: Option<PathBuf>,

    /// If set, executes the output program, rather than displaying it. For asm or executes the binary, for other targets, runs an interpreter
    #[arg(short = 'x', long, value_name = "execute", allow_hyphen_values = true, num_args = 0..)]
    execute: Option<Vec<String>>,

    /// Optional runtime file. Defaults to runtime/stub.rs
    #[arg(short, long, value_name = "runtime")]
    runtime: Option<PathBuf>,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, ValueEnum)]
enum Target {
    /// Raw AST
    AST,
    /// Resolved AST
    ResolvedAST,
    /// SSA
    SSA,
    /// x86_64 Assembly Code
    Asm,
    /// Binary executable
    Exe,
}
use Target::*;

fn run_cli(cli: &Cli) -> Result<(), String> {
    let inp =
        read_file(Path::new(&cli.input_file)).map_err(|e| format!("Error reading file: {}", e))?;
    let file_info = FileInfo::new(&inp);
    let raw_ast =
        ProgParser::new().parse(&inp).map_err(|e| format!("Error parsing program: {}", e))?;
    match cli.target {
        Some(AST) => {
            if let Some(ref args) = cli.execute {
                let value = interp::ast::Machine::run(&raw_ast, args)
                    .map_err(|e| format!("Error interpreting program: {}", e))?;
                println!("{}", value);
            } else {
                println!("{}", raw_ast);
            }
            return Ok(());
        }
        _ => {}
    }
    let mut resolver = Resolver::new();
    let resolved_ast = resolver
        .resolve_prog(raw_ast)
        .map_err(|e| format!("Error resolving ast: {}", file_info.report_error(e)))?;
    match cli.target {
        Some(ResolvedAST) => {
            if let Some(ref args) = cli.execute {
                let value = interp::ast::Machine::run(&resolved_ast, args)
                    .map_err(|e| format!("Error interpreting program: {}", e))?;
                println!("{}", value);
            } else {
                println!("{}", resolved_ast);
            }
            return Ok(());
        }
        _ => {}
    }
    let mut lowerer = Lowerer::from(resolver);
    let ssa = lowerer.lower_prog(resolved_ast);
    match cli.target {
        Some(SSA) => {
            if let Some(ref args) = cli.execute {
                let mut interp = interp::ssa::Interp::new();
                let value = interp
                    .run(&ssa, args)
                    .map_err(|e| format!("Error interpreting program: {}", e))?;
                println!("{}", value);
            } else {
                println!("{}", ssa);
            }
            return Ok(());
        }
        _ => {}
    }
    let mut emitter = Emitter::from(lowerer);
    emitter.emit_prog(&ssa);
    let asm = emitter.to_asm();
    let txt = instrs_to_string(&asm);
    match (cli.target, &cli.execute) {
        // Assembly and not execute
        (Some(Asm) | None, None) => {
            println!("{}", txt);
            return Ok(());
        }
        _ => {}
    }
    // if the target is assembly and execute is true, we treat it the same as Exe execute.
    // target is Exe, may want to execute
    let rt = cli.runtime.clone().unwrap_or(PathBuf::from("runtime/stub.rs"));
    let o_dir = PathBuf::from("runtime");
    let exe_fname = cli.output.clone().unwrap_or(PathBuf::from("runtime/stub.exe"));
    link(&txt, &rt, &o_dir, &exe_fname)?;
    if let Some(ref args) = cli.execute {
        run(&exe_fname, args, &mut std::io::stdout())?;
    }
    Ok(())
}
fn main() {
    let cli = Cli::parse();

    match run_cli(&cli) {
        Ok(()) => {}
        Err(e) => {
            eprintln!("{}", e);
            std::process::exit(1);
        }
    };
}
