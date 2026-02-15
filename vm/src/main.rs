use clap::Parser as ClapParser;
use std::{
    fs,
    io::{self, Write},
    process,
};

use heap::HeapSettings;
use parser::{Lexer, Parser};

use vm::{compiler0::Compiler, interpreter, materialize, special, VM};

#[derive(ClapParser, Debug)]
#[command(author, version, about, long_about = None)]
struct Cli {
    /// Input source files to execute in order
    #[arg(required = false, help = "The .ktt files to execute")]
    files: Vec<String>,

    /// Start REPL after executing files (default if no files)
    #[arg(long, help = "Force REPL mode after file execution")]
    repl: bool,
}

fn main() {
    let cli = Cli::parse();

    let mut vm = special::bootstrap(HeapSettings::default());

    for filename in &cli.files {
        let source_code = match fs::read_to_string(filename) {
            Ok(content) => content,
            Err(err) => {
                eprintln!("Error reading file '{}': {}", filename, err);
                process::exit(1);
            }
        };

        match execute_source(&mut vm, &source_code) {
            Ok(value) => {
                println!("{:?}", value);
            }
            Err(err) => {
                eprintln!("Error executing {}: {}", filename, err);
                process::exit(1);
            }
        }
    }

    if cli.repl || cli.files.is_empty() {
        run_repl(&mut vm);
    }
}

fn run_repl(vm: &mut VM) {
    println!("Kette VM REPL");
    println!("Type 'exit' to quit.");

    let stdin = io::stdin();
    let mut stdout = io::stdout();
    let mut input_buffer = String::new();

    loop {
        print!("> ");
        if let Err(err) = stdout.flush() {
            eprintln!("Error flushing stdout: {}", err);
            break;
        }

        input_buffer.clear();
        match stdin.read_line(&mut input_buffer) {
            Ok(0) => break,
            Ok(_) => {
                let input = input_buffer.trim();
                if input == "exit" {
                    break;
                }
                if input.is_empty() {
                    continue;
                }

                match execute_source(vm, &input_buffer) {
                    Ok(value) => println!("{:?}", value),
                    Err(err) => eprintln!("Error: {}", err),
                }
            }
            Err(err) => {
                eprintln!("Error reading input: {}", err);
                break;
            }
        }
    }
}

fn execute_source(vm: &mut VM, source: &str) -> Result<object::Value, String> {
    let lexer = Lexer::from_str(source);
    let exprs: Vec<parser::ast::Expr> = Parser::new(lexer)
        .map(|r| r.map_err(|e| e.to_string()))
        .collect::<Result<_, _>>()?;

    let code_desc = Compiler::compile(&exprs).map_err(|e| e.to_string())?;
    let code = materialize::materialize(vm, &code_desc);
    interpreter::interpret(vm, code).map_err(format_runtime_error)
}

fn format_runtime_error(err: interpreter::RuntimeError) -> String {
    match err {
        interpreter::RuntimeError::MessageNotUnderstood {
            receiver,
            message,
        } => {
            let msg = value_to_string(message)
                .unwrap_or_else(|| format!("{:?}", message));
            let recv = value_to_string(receiver)
                .unwrap_or_else(|| format!("{:?}", receiver));
            format!(
                "MessageNotUnderstood {{ receiver: {recv}, message: {msg} }}"
            )
        }
        other => format!("{:?}", other),
    }
}

fn value_to_string(value: object::Value) -> Option<String> {
    if !value.is_ref() {
        if value.is_fixnum() {
            let n = unsafe { value.to_i64() };
            return Some(n.to_string());
        }
        return None;
    }

    let header: &object::Header = unsafe { value.as_ref() };
    if header.object_type() == object::ObjectType::Str {
        let s: &object::VMString = unsafe { value.as_ref() };
        return Some(unsafe { s.as_str() }.to_string());
    }

    None
}
