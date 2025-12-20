use kette::{
    Array, Block, BytecodeCompiler, ExecutionState, ExecutionStateInfo,
    HeapCreateInfo, Instruction, Interpreter, Parser, Tagged, ThreadProxy, VM,
    VMCreateInfo, VMThread, Value,
};
use std::{env, fs, process};

// We create a helper to define the parser's initial "boot" script.
// This tells the parser object to parse its internal buffer.
fn execute_parser_code(parser: Value) -> Block {
    let instructions = vec![
        Instruction::PushValue { value: parser },
        Instruction::SendNamed { message: "parse" },
    ];

    Block { instructions }
}

fn main() {
    let args: Vec<String> = env::args().collect();

    if args.len() < 2 {
        eprintln!("Usage: {} <file.ktt>", args[0]);
        process::exit(1);
    }

    let filename = &args[1];

    let source_code = match fs::read_to_string(filename) {
        Ok(content) => content,
        Err(err) => {
            eprintln!("Error reading file '{}': {}", filename, err);
            process::exit(1);
        }
    };

    tracing_subscriber::fmt()
        .with_env_filter(tracing_subscriber::EnvFilter::from_default_env())
        .with_span_events(tracing_subscriber::fmt::format::FmtSpan::EXIT)
        .init();

    let vm = VM::new(VMCreateInfo {
        image: None,
        heap: HeapCreateInfo {
            size: 1024 * 64 * 4,
            ..Default::default()
        },
    });

    let main_proxy = vm.new_proxy();
    let mut heap = main_proxy.shared.heap.create_proxy();

    let state = ExecutionState::new(&ExecutionStateInfo {
        stack_size: 128,
        return_stack_size: 128,
    });

    let main_thread = VMThread::new_main();
    let thread_proxy = ThreadProxy(main_thread.inner);

    let proxy = vm.new_proxy();

    let mut parser = Box::new(Parser::new_object(
        &proxy,
        &mut heap,
        source_code.as_bytes(),
    ));

    let parser_obj = Tagged::new_ptr(parser.as_mut());

    let parser_code = execute_parser_code(parser_obj.into());

    let mut interpreter = Interpreter::new(proxy, thread_proxy, heap, state);

    for instruction in parser_code.instructions {
        interpreter.execute_single_bytecode(instruction);
    }

    // SAFETY: We expect the parser to leave exactly one Array on the stack upon success.
    let body = unsafe {
        interpreter
            .state
            .pop()
            .expect("Parser did not return a body")
            .as_handle_unchecked()
            .cast::<Array>()
    };

    let compiled = BytecodeCompiler::compile(&interpreter.vm.shared, body);

    let quotation = interpreter.heap.allocate_quotation(body, &compiled, 0, 0);

    // SAFETY: Promoting a newly allocated pointer to a handle is safe here.
    let quotation = unsafe { quotation.promote_to_handle() };

    interpreter.add_quotation(quotation);

    tracing::debug!("RUN");
    interpreter.execute();
}
