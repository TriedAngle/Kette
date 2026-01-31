use clap::Parser as ClapParser;
use kette::{
    Allocator, Array, BytecodeCompiler, BytecodeWriter, ExecutionResult,
    ExecutionState, ExecutionStateInfo, Handle, HeapSettings, Interpreter,
    ThreadProxy, VM, VMCreateInfo, VMThread,
};
use std::{
    fs,
    io::{self, Write},
    process,
};

#[derive(ClapParser, Debug)]
#[command(author, version, about, long_about = None)]
struct Cli {
    /// Input kette source files to execute in order
    #[arg(required = false, help = "The .ktt files to execute")]
    files: Vec<String>,

    /// Start REPL after executing files (default behavior if no files provided)
    #[arg(long, short, help = "Force REPL mode after file execution")]
    repl: bool,
}

fn main() {
    let cli = Cli::parse();

    tracing_subscriber::fmt()
        .with_env_filter(tracing_subscriber::EnvFilter::from_default_env())
        .with_span_events(tracing_subscriber::fmt::format::FmtSpan::EXIT)
        .init();

    let vm = VM::new(VMCreateInfo {
        image: None,
        heap: HeapSettings {
            ..Default::default()
        },
    });

    let main_proxy = vm.proxy();
    let heap = main_proxy.shared.heap.proxy();

    let state = ExecutionState::new(&ExecutionStateInfo {
        stack_size: 128,
        return_stack_size: 128,
    });

    let main_thread = VMThread::new_main();
    let thread_proxy = ThreadProxy(main_thread.inner);
    let proxy = vm.proxy();

    let mut interpreter = Interpreter::new(proxy, thread_proxy, heap, state);

    // FILES:
    for filename in &cli.files {
        tracing::debug!("Loading file: {}", filename);

        let source_code = match fs::read_to_string(filename) {
            Ok(content) => content,
            Err(err) => {
                eprintln!("Error reading file '{}': {}", filename, err);
                process::exit(1);
            }
        };

        match execute_source(&mut interpreter, &source_code) {
            Ok(_) => {
                // Print stack after file execution
                interpreter.print_stack();
            }
            Err(e) => {
                eprintln!("Error executing {}: {}", filename, e);
                process::exit(1);
            }
        }
    }

    // REPL:
    if cli.repl || cli.files.is_empty() {
        run_repl(&mut interpreter);
    }
}

fn run_repl(interpreter: &mut Interpreter) {
    println!("Kette REPL");
    println!("Type 'exit' to quit.");

    let stdin = io::stdin();
    let mut stdout = io::stdout();
    let mut input_buffer = String::new();

    loop {
        print!("> ");
        if let Err(e) = stdout.flush() {
            eprintln!("Error flushing stdout: {}", e);
            break;
        }

        input_buffer.clear();

        match stdin.read_line(&mut input_buffer) {
            Ok(0) => break, // EOF
            Ok(_) => {
                let input = input_buffer.trim();
                if input == "exit" {
                    break;
                }
                if input.is_empty() {
                    continue;
                }

                // SNAPSHOT:
                let saved_state = interpreter.state.clone();
                let saved_activations = interpreter.activations.clone();

                match execute_source(interpreter, &input_buffer) {
                    Ok(_) => {
                        interpreter.print_stack();
                    }
                    Err(msg) => {
                        eprintln!("Error: {}", msg);

                        interpreter.state = saved_state;
                        interpreter.activations = saved_activations;
                        interpreter.print_stack();
                        interpreter.cache = None;
                    }
                }
            }
            Err(e) => {
                eprintln!("Error reading input: {}", e);
                break;
            }
        }
    }
}

/// Helper to Parse, Compile, and Execute a chunk of source code.
fn execute_source(
    interpreter: &mut Interpreter,
    source: &str,
) -> Result<(), String> {
    // Allocate parser on the GC heap (not Rust heap via Box)
    let parser = interpreter
        .heap
        .allocate_parser(&interpreter.vm.shared.strings, source.as_bytes());

    let parse_msg = interpreter
        .vm
        .intern_string_message("parse", &mut interpreter.heap);

    let constants = vec![parser.as_value(), parse_msg.as_value()];

    let mut writer = BytecodeWriter::new();
    // PushConstant(0) - parser object
    writer.emit_push_constant(0);
    // Send(1) - "parse" message
    writer.emit_send(1, 0);
    writer.emit_return();

    let dummy_body = interpreter.heap.allocate_array(&[]);

    let boot_code = interpreter.heap.allocate_code(
        &constants,
        &writer.into_inner(),
        1, // 1 Send site (the "parse" call)
        dummy_body,
        unsafe { Handle::null() },
    );

    let boot_map = interpreter.heap.allocate_executable_map(boot_code, 0, 0);

    let boot_quotation = interpreter
        .heap
        .allocate_quotation(boot_map, unsafe { Handle::null() });

    interpreter.add_quotation(boot_quotation);

    match interpreter.execute() {
        ExecutionResult::Normal => {}
        ExecutionResult::Panic(msg) => {
            return Err(format!("Parser Panic: {}", msg));
        }
        res => return Err(format!("Parser abnormal exit: {:?}", res)),
    }

    let body_val = match interpreter.state.pop() {
        Some(v) => v,
        None => {
            return Err("Parser did not return a value (Empty Stack)".into());
        }
    };

    if body_val == interpreter.vm.shared.specials.false_object.as_value() {
        return Err("Parsing failed (Syntax Error)".into());
    }

    let body_array = unsafe { body_val.as_handle_unchecked().cast::<Array>() };

    let code = BytecodeCompiler::compile(
        &interpreter.vm.shared,
        &mut interpreter.heap,
        body_array,
    );

    let code_map = interpreter.heap.allocate_executable_map(code, 0, 0);

    let quotation = interpreter
        .heap
        .allocate_quotation(code_map, unsafe { Handle::null() });

    interpreter.add_quotation(quotation);

    match interpreter.execute() {
        ExecutionResult::Normal => Ok(()),
        ExecutionResult::Panic(msg) => Err(format!("Panic: {}", msg)),
        res => Err(format!("Abnormal exit: {:?}", res)),
    }
}
