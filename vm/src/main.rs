use clap::Parser as ClapParser;
use std::{
    fs,
    io::{self, Write},
    process,
};

use heap::HeapSettings;
use parser::{Lexer, Parser};

use vm::{compiler0, interpreter, materialize, special, VM};

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
                print_value(&mut vm, value);
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
                    Ok(value) => print_value(vm, value),
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

    let results: Vec<_> = Parser::new(lexer).collect();

    let errors: Vec<String> = results
        .iter()
        .filter_map(|r| r.as_ref().err())
        .map(|e| e.to_string())
        .collect();

    if !errors.is_empty() {
        return Err(errors.join("\n"));
    }

    let exprs: Vec<parser::ast::Expr> =
        results.into_iter().map(|r| r.unwrap()).collect();

    let code_desc =
        compiler0::Compiler::compile(&exprs).map_err(|e| e.to_string())?;
    let code = materialize::materialize(vm, &code_desc);

    interpreter::interpret(vm, code).map_err(format_runtime_error)
}

fn print_value(vm: &mut VM, value: object::Value) {
    if let Some(text) = value_to_string(value) {
        println!("{}", text);
        return;
    }

    if let Some(text) = try_to_string(vm, value) {
        println!("{}", text);
        return;
    }

    println!("{:?}", value);
}

fn try_to_string(vm: &mut VM, value: object::Value) -> Option<String> {
    let mut builder = bytecode::BytecodeBuilder::new();
    builder.load_constant(0);
    builder.send(1, 0, 0, 0);
    builder.local_return();

    let code_desc = compiler0::CodeDesc {
        bytecode: builder.into_bytes(),
        constants: vec![
            compiler0::ConstEntry::Value(value),
            compiler0::ConstEntry::Symbol("toString".to_string()),
        ],
        register_count: 1,
        arg_count: 0,
        temp_count: 0,
        feedback_count: 1,
    };

    let code = materialize::materialize(vm, &code_desc);
    let result = interpreter::interpret(vm, code).ok()?;
    value_to_string(result)
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
        interpreter::RuntimeError::UndefinedGlobal { name } => {
            format!("UndefinedGlobal {{ name: {name} }}")
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
