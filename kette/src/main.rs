use std::fs;
use std::io::{self, BufRead, Write};
use std::path::{Path, PathBuf};
use std::process;
use std::sync::Arc;

use clap::{ArgAction, Parser};
use parking_lot::Mutex;

use kette::{
    CodeHeap, Context, ContextConfig, Quotation, Tagged,
    add_primitives,
};

#[derive(Parser, Debug)]
#[command(author, version, about = "A stack-based language interpreter")]
struct Args {
    #[arg(short, long, value_name = "FILE")]
    file: Option<PathBuf>,

    #[arg(short, long, action = ArgAction::SetTrue)]
    no_startup: bool,

    #[arg(short, long, action = ArgAction::SetTrue)]
    interactive: bool,
}

fn main() {
    let args = Args::parse();

    let code_heap = Arc::new(Mutex::new(CodeHeap::new()));
    let config = ContextConfig {
        data_size: 1024,
        retian_size: 1024,
        name_size: 1024,
    };
    let mut ctx = Context::new(&config, code_heap);
    add_primitives(&mut ctx);

    println!("Started Kette in Terminal");

    let mut loaded_file = false;

    if !args.no_startup {
        let mut startup_file = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        startup_file.push("..");
        startup_file.push("core");
        startup_file.push("stage0.ktt");
        if Path::new(&startup_file).exists() {
            match load_and_execute_file(&mut ctx, &startup_file) {
                Ok(_) => {
                    println!("Loaded startup file: {}", startup_file.display());
                }
                Err(e) => {
                    eprintln!("Error loading startup file: {}", e);
                    process::exit(1);
                }
            }
        } else {
            eprintln!("Startup File not found: {}", startup_file.display());
            process::exit(1);
        }
    }

    if let Some(user_file) = args.file.clone() {
        if Path::new(&user_file).exists() {
            match load_and_execute_file(&mut ctx, &user_file) {
                Ok(_) => {
                    println!("Loaded startup File: {}", user_file.display());
                    loaded_file = true;
                }
                Err(e) => {
                    eprintln!("Error loading File: {}", e);
                    if args.file.is_some() {
                        process::exit(1);
                    }
                }
            }
        } else if args.file.is_some() {
            eprintln!("File not found: {}", user_file.display());
            process::exit(1);
        }
    }

    let should_run_repl = args.interactive || !loaded_file;
    if should_run_repl {
        run_repl(&mut ctx);
    }
}

fn load_and_execute_file(
    ctx: &mut Context,
    file_path: &Path,
) -> io::Result<()> {
    let content = fs::read_to_string(file_path)?;
    let input = ctx.gc.allocate_string(&content);
    ctx.reset_parser(input);
    let tokens = ctx.parse_until(None);
    if !tokens.is_empty() {
        let quotation = ctx.gc.allocate_quotation(&tokens);
        ctx.execute(quotation.to_ptr() as *const Quotation);
    }

    Ok(())
}

fn run_repl(ctx: &mut Context) {
    println!("Interactive REPL mode. Type 'quit' or 'exit' to exit.");
    let stdin = io::stdin();
    let mut stdout = io::stdout();
    let mut input = String::new();
    let mut line_num = 1;

    loop {
        print!("IN #{}> ", line_num);
        stdout.flush().unwrap();

        input.clear();
        if stdin.lock().read_line(&mut input).unwrap() == 0 {
            break; // EOF
        }

        let input_trimmed = input.trim();
        if input_trimmed.is_empty() {
            continue;
        }

        if input_trimmed == "quit" || input_trimmed == "exit" {
            break;
        }

        execute_string(ctx, &input);

        print_stack(ctx);

        line_num += 1;
    }

    println!("Goodbye!");
}

fn execute_string(ctx: &mut Context, input: &str) {
    let input = ctx.gc.allocate_string(input);
    ctx.reset_parser(input);

    let tokens = ctx.parse_until(None);
        let quotation = ctx.gc.allocate_quotation(&tokens);
        ctx.execute(quotation.to_ptr() as *const Quotation);
        let codes = ctx.codes.lock();
        let code = codes
            .get_code_for_quotation(quotation.to_ptr() as _)
            .unwrap();

        println!("parsed: {:?}", tokens);
        println!("compiled: {:?}", code);
}

fn print_stack(ctx: &Context) {
    let stack_size = {
        let data_ptr = ctx.data.current;
        let data_start = ctx.data.start;
        (data_ptr as usize - data_start as usize)
            / std::mem::size_of::<Tagged>()
    };

    println!("Stack size: {}", stack_size);
}
