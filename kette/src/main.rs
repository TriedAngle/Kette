use clap::Parser as ClapParser;
use kette::{
    Allocator, Array, Block, BytecodeCompiler, ExecutionState,
    ExecutionStateInfo, HeapSettings, Instruction, Interpreter, Parser, Tagged,
    ThreadProxy, VM, VMCreateInfo, VMThread, Value,
};
use std::{fs, process};

#[derive(ClapParser, Debug)]
#[command(author, version, about, long_about = None)]
struct Cli {
    /// Input kette source files to execute in order
    #[arg(required = true, help = "The .ktt files to execute")]
    files: Vec<String>,
}

fn execute_parser_code(parser: Value) -> Block {
    let instructions = vec![
        Instruction::PushValue { value: parser },
        Instruction::SendNamed { message: "parse" },
    ];

    Block { instructions }
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

    let main_proxy = vm.new_proxy();

    let heap = main_proxy.shared.heap.proxy();

    let state = ExecutionState::new(&ExecutionStateInfo {
        stack_size: 128,
        return_stack_size: 128,
    });

    let main_thread = VMThread::new_main();
    let thread_proxy = ThreadProxy(main_thread.inner);
    let proxy = vm.new_proxy();

    let mut interpreter = Interpreter::new(proxy, thread_proxy, heap, state);

    for filename in &cli.files {
        tracing::debug!("Loading file: {}", filename);

        let source_code = match fs::read_to_string(filename) {
            Ok(content) => content,
            Err(err) => {
                eprintln!("Error reading file '{}': {}", filename, err);
                process::exit(1);
            }
        };

        let parser_proxy = vm.new_proxy();

        let mut parser = Box::new(Parser::new_object(
            &parser_proxy,
            &mut interpreter.heap,
            source_code.as_bytes(),
        ));

        let parser_obj = Tagged::new_ptr(parser.as_mut());
        let parser_code = execute_parser_code(parser_obj.into());

        for instruction in parser_code.instructions {
            interpreter.execute_single_bytecode(instruction);
        }

        // SAFETY: this is safe
        let body = unsafe {
            interpreter
                .state
                .pop()
                .expect("Parser did not return a body")
                .as_handle_unchecked()
                .cast::<Array>()
        };

        let compiled = BytecodeCompiler::compile(&interpreter.vm.shared, body);

        let quotation =
            interpreter.heap.allocate_quotation(body, &compiled, 0, 0);

        interpreter.add_quotation(quotation);

        tracing::debug!("Executing {}", filename);
        interpreter.execute();
    }
}
