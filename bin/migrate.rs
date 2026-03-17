use clap::Parser;
use colored::{Color, Colorize as _};
use diamondback::{ast::Expr, parser::ProgParser};
use std::{
    fs::File,
    io::{self, Write as _},
    path::PathBuf,
};
use walkdir::WalkDir;

/// Automatically migrate example(s) to the new `.dbk` format.
///
/// The only argument is a path to example(s). Could be either:
///
/// - A single example file.
///
/// - Directory containing all examples. Could be nested.
///
/// The example file(s) should end with `.adder`, `.boa`, or `.cobra`.
///
/// The output will be saved in the same directory as the example file(s),
/// with the same name, but with a `.dbk` extension.
#[derive(Parser, Debug)]
#[command(about, long_about)]
struct Cli {
    /// A path to example(s). Could be either:
    ///
    /// - A single example file.
    ///
    /// - Directory containing all examples. Could be nested.
    example_path: PathBuf,
}

struct Task {
    src: PathBuf,
    dst: PathBuf,
    is_overwrite: bool,
}
impl Task {
    fn new(src: PathBuf) -> Option<Self> {
        let true = src.exists() else { None? };
        let src_ext = src.extension()?;
        let true = (src_ext == "adder" || src_ext == "boa" || src_ext == "cobra") else { None? };
        let dst = src.with_extension("dbk");
        let is_overwrite = dst.exists();
        Some(Self { src, dst, is_overwrite })
    }

    fn run(&self) -> io::Result<()> {
        // read the source file
        let mut source = std::fs::read_to_string(&self.src)?;
        let prog = ProgParser::new()
            .parse(&source)
            .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, format!("{}", e)))?;
        let param = prog.param.0;
        let body_start = match prog.body {
            Expr::Num(_, loc)
            | Expr::Bool(_, loc)
            | Expr::Var(_, loc)
            | Expr::Prim { loc, .. }
            | Expr::Let { loc, .. }
            | Expr::If { loc, .. }
            | Expr::FunDefs { loc, .. }
            | Expr::Call { loc, .. } => loc.start_ix,
        };

        // insert the param at the body start in source
        source.insert_str(body_start, &format!("let {} = {}[0] in\n  ", param, param));

        // write the destination file
        let mut file = File::create(&self.dst)?;
        file.write_all(source.as_bytes())?;
        Ok(())
    }

    fn remove_old(&self) -> io::Result<()> {
        std::fs::remove_file(&self.src)?;
        Ok(())
    }
}

fn prompt(message: &str) -> bool {
    print!("{} [y/N] ", message);
    std::io::stdout().flush().unwrap();
    let mut input = String::new();
    std::io::stdin().read_line(&mut input).unwrap();
    input.trim().to_lowercase() == "y"
}

fn main() {
    let cli = Cli::parse();
    let example_path = cli.example_path;
    let mut tasks = Vec::new();
    if example_path.is_file() {
        if let Some(task) = Task::new(example_path) {
            tasks.push(task);
        }
    } else if example_path.is_dir() {
        // walk the directory
        for entry in WalkDir::new(example_path) {
            let entry = entry.unwrap();
            let path = entry.path();
            if path.is_file() {
                if let Some(task) = Task::new(path.to_path_buf()) {
                    tasks.push(task);
                }
            }
        }
    }
    println!("Found {} tasks:", tasks.len());
    for task in tasks.iter() {
        println!(
            "\t{} {} {} {}",
            "-".color(Color::Blue),
            format!("{}", task.src.display()).color(Color::BrightBlack),
            "->".color(Color::Blue),
            format!("{}", task.dst.display()).color(if task.is_overwrite {
                Color::BrightRed
            } else {
                Color::White
            })
        );
    }

    // prompt user to confirm
    let proceed = prompt("Are you sure you want to proceed?");
    if !proceed {
        println!("Aborting.");
        return;
    }

    for task in tasks.iter() {
        task.run().expect("Failed to run migration");
    }

    // prompt user to remove old source files
    let remove = prompt("Do you want to remove the old source files?");
    if remove {
        for task in tasks.iter() {
            task.remove_old().expect("Failed to remove old source file");
        }
    }
}
