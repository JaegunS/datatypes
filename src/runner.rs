use std::fs::File;
use std::io::prelude::*;
use std::io::{BufReader, Read, Write};
use std::path::Path;
use std::process::{Command, Stdio};

use crate::ast::BoundProg;
use crate::compile;
use crate::frontend::Resolver;
use crate::middle_end::Lowerer;
use crate::ssa::Program;

fn handle_errs(r: Result<String, String>) {
    match r {
        Ok(s) => println!("{}", s),
        Err(e) => {
            eprintln!("{}", e);
            std::process::exit(1);
        }
    }
}

/// used in student tests
pub fn emit_ast(p: &Path) -> Result<(Resolver, BoundProg), String> {
    let (resolver, ast) =
        compile::frontend(&read_file(p).map_err(|e| format!("Error reading file: {}", e))?)?;
    Ok((resolver, ast))
}

/// used in student tests
pub fn emit_ssa(p: &Path) -> Result<(Lowerer, Program), String> {
    let (resolver, ast) = emit_ast(p)?;
    let (lowerer, ssa) = compile::middle_end(resolver, ast)?;
    Ok((lowerer, ssa))
}

pub fn emit_assembly(p: &Path) {
    handle_errs(compile_file(p))
}

pub fn compile_and_run_file<W, S>(
    p: &Path, dir: &Path, args: impl IntoIterator<Item = S>, out: &mut W,
) -> Result<(), String>
where
    W: std::io::Write,
    S: Into<String>,
{
    let asm = compile_file(p)?;
    link_and_run(&asm, Path::new("runtime/stub.rs"), dir, args, out)
}

fn compile_file(p: &Path) -> Result<String, String> {
    compile::compile(&read_file(p).map_err(|e| format!("Error reading file: {}", e))?)
}

pub fn read_file(p: &Path) -> Result<String, std::io::Error> {
    let mut f = File::open(p)?;
    let mut buf = String::new();
    f.read_to_string(&mut buf)?;
    Ok(buf)
}

pub fn link(
    assembly: &str, runtime_file: &Path, dir: &Path, exe_fname: &Path,
) -> Result<(), String> {
    let (nasm_format, lib_name) = if cfg!(target_os = "linux") {
        ("elf64", "libcompiled_code.a")
    } else if cfg!(target_os = "macos") {
        ("macho64", "libcompiled_code.a")
    } else {
        panic!("Runner script only supports linux and macos")
    };

    let asm_fname = dir.join("compiled_code.s");
    let obj_fname = dir.join("compiled_code.o");
    let lib_fname = dir.join(lib_name);

    // first put the assembly in a new file compiled_code.s
    let mut asm_file = File::create(&asm_fname).map_err(|e| e.to_string())?;
    asm_file.write(assembly.as_bytes()).map_err(|e| e.to_string())?;
    asm_file.flush().map_err(|e| e.to_string())?;

    // nasm -fFORMAT -o compiled_code.o compiled_code.s
    let nasm_out = Command::new("nasm")
        .arg("-f")
        .arg(nasm_format)
        .arg("-o")
        .arg(&obj_fname)
        .arg(&asm_fname)
        .output()
        .map_err(|e| format!("nasm err: {}", e))?;
    if !nasm_out.status.success() {
        return Err(format!(
            "Failure in nasm call: {}\n{}",
            nasm_out.status,
            std::str::from_utf8(&nasm_out.stderr).expect("nasm produced invalid UTF-8")
        ));
    }

    // ar r libcompiled_code.a compiled_code.o
    let ar_out = Command::new("ar")
        .arg("rus")
        .arg(lib_fname)
        .arg(&obj_fname)
        .output()
        .map_err(|e| format!("ar err: {}", e))?;
    if !ar_out.status.success() {
        return Err(format!(
            "Failure in ar call:\n{}\n{}",
            ar_out.status,
            std::str::from_utf8(&ar_out.stderr).expect("ar produced invalid UTF-8")
        ));
    }

    // rustc stub.rs -L tmp
    let rustc_out = if cfg!(target_os = "macos") {
        Command::new("rustc")
            .arg(runtime_file)
            .arg("--target")
            .arg("x86_64-apple-darwin")
            .arg("-L")
            .arg(dir)
            .arg("-o")
            .arg(&exe_fname)
            .output()
            .map_err(|e| format!("rustc err: {}", e))?
    } else {
        Command::new("rustc")
            .arg(runtime_file)
            .arg("-L")
            .arg(dir)
            .arg("-o")
            .arg(&exe_fname)
            .output()
            .map_err(|e| format!("rustc err: {}", e))?
    };
    if !rustc_out.status.success() {
        Err(format!(
            "Failure in rustc call: {}\n{}",
            rustc_out.status,
            std::str::from_utf8(&rustc_out.stderr).expect("rustc produced invalid UTF-8")
        ))
    } else {
        Ok(())
    }
}

pub fn run<W, S>(
    exe_fname: &Path, args: impl IntoIterator<Item = S>, out: &mut W,
) -> Result<(), String>
where
    W: std::io::Write,
    S: Into<String>,
{
    let mut child = Command::new(&exe_fname)
        .args(args.into_iter().map(|s| s.into()))
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|e| format!("{}", e))?;
    let compiled_out =
        BufReader::new(child.stdout.take().expect("Failed to capture compiled code's stdout"));
    let compiled_err =
        BufReader::new(child.stderr.take().expect("Failed to capture compiled code's stderr"));

    for line in compiled_out.lines() {
        let line = line.map_err(|e| format!("{}", e))?;
        writeln!(out, "{}", line).map_err(|e| format!("I/O error: {}", e))?;
    }

    let status = child.wait().map_err(|e| format!("Error waiting for child process {}", e))?;
    if !status.success() {
        let mut stderr = String::new();
        for line in compiled_err.lines() {
            stderr.push_str(&format!("{}\n", line.unwrap()));
        }
        return Err(format!(
            "Error code {} when running compiled code Stderr:\n{}",
            status, stderr
        ));
    }
    Ok(())
}

pub fn link_and_run<W, S>(
    assembly: &str, runtime_file: &Path, dir: &Path, args: impl IntoIterator<Item = S>, out: &mut W,
) -> Result<(), String>
where
    W: std::io::Write,
    S: Into<String>,
{
    let exe_fname = dir.join("main.exe");
    link(assembly, runtime_file, dir, &exe_fname)?;
    run(&exe_fname, args, out)
}
