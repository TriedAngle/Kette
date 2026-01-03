use clap::Parser as ClapParser;
use kette::{
    Allocator, Array, BytecodeCompiler, ExecutionState, ExecutionStateInfo,
    Handle, HeapSettings, Instruction, Interpreter, OpCode, Parser, Tagged,
    ThreadProxy, VM, VMCreateInfo, VMThread,
};
use std::{fs, process};

#[derive(ClapParser, Debug)]
#[command(author, version, about, long_about = None)]
struct Cli {
    /// Input kette source files to execute in order
    #[arg(required = true, help = "The .ktt files to execute")]
    files: Vec<String>,
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

    for filename in &cli.files {
        tracing::debug!("Loading file: {}", filename);

        let source_code = match fs::read_to_string(filename) {
            Ok(content) => content,
            Err(err) => {
                eprintln!("Error reading file '{}': {}", filename, err);
                process::exit(1);
            }
        };

        let parser_proxy = vm.proxy();

        let mut parser = Box::new(Parser::new_object(
            &parser_proxy,
            &mut interpreter.heap,
            source_code.as_bytes(),
        ));

        let parser_obj = Tagged::new_ptr(parser.as_mut());

        // Intern the "parse" message
        let parse_msg = interpreter
            .vm
            .intern_string_message("parse", &mut interpreter.heap);

        let constants = vec![parser_obj.as_value(), parse_msg.as_value()];

        let instructions = vec![
            Instruction::new_data(OpCode::PushConstant, 0),
            Instruction::new_data(OpCode::Send, 1),
            Instruction::new(OpCode::Return),
        ];

        // Allocate a dummy body (empty array) just to satisfy the Quotation
        let dummy_body = interpreter.heap.allocate_array(&[]);

        // Allocate the Code object
        let boot_code = interpreter.heap.allocate_code(
            &constants,
            &instructions,
            dummy_body,
        );

        let boot_map =
            interpreter.heap.allocate_executable_map(boot_code, 0, 0);

        // Create the Bootstrap Quotation
        let boot_quotation = interpreter
            .heap
            .allocate_quotation(boot_map, unsafe { Handle::null() });

        // 3. Execute the Parser
        interpreter.add_quotation(boot_quotation);
        interpreter.execute();

        // SAFETY: this is safe
        let body = unsafe {
            interpreter
                .state
                .pop()
                .expect("Parser did not return a body")
                .as_handle_unchecked()
                .cast::<Array>()
        };

        let code = BytecodeCompiler::compile(
            &interpreter.vm.shared,
            &mut interpreter.heap,
            body,
        );

        let code_map = interpreter.heap.allocate_executable_map(code, 0, 0);

        let quotation = interpreter
            .heap
            .allocate_quotation(code_map, unsafe { Handle::null() });

        interpreter.add_quotation(quotation);

        tracing::debug!("Executing {}", filename);
        interpreter.execute();
    }
}
