use kette::{
    Array, Block, BytecodeCompiler, ExecutionState, ExecutionStateInfo,
    HeapCreateInfo, Instruction, Interpreter, Parser, Tagged, ThreadProxy, VM,
    VMCreateInfo, VMThread, Value,
};

const CODE: &str = r#"
5 77 fixnum+ fixnum>utf8-bytes bytearray-println
"#;

fn execute_parser_code(value: Value) -> Block {
    let instructions = vec![
        Instruction::PushValue { value },
        Instruction::SendNamed {
            message: "parse-full",
        },
    ];

    Block { instructions }
}

fn main() {
    let vm = VM::new(VMCreateInfo {
        image: None,
        heap: HeapCreateInfo {
            size: 1024 * 32 * 2,
            ..Default::default()
        },
    });

    // TODO: use consistent naming
    let main_proxy = vm.new_proxy();
    let mut heap = main_proxy.shared.heap.create_proxy();

    let state = ExecutionState::new(&ExecutionStateInfo {
        stack_size: 128,
        return_stack_size: 128,
    });

    // TODO: make create function for this.
    let main_thread = VMThread::new_main();
    let thread_proxy = ThreadProxy(main_thread.inner);

    let proxy = vm.new_proxy();

    let mut parser =
        Box::new(Parser::new_object(&proxy, &mut heap, CODE.as_bytes()));

    let parser_obj = Tagged::new_ptr(parser.as_mut());

    let parser_code = execute_parser_code(parser_obj.into());

    let mut interpreter = Interpreter::new(proxy, thread_proxy, heap, state);

    for instruction in parser_code.instructions {
        interpreter.execute_bytecode(instruction);
    }

    // SAFETY: this is guaranteed by the contract
    let array = unsafe {
        interpreter
            .state
            .pop()
            .expect("exists")
            .as_handle_unchecked()
            .cast::<Array>()
    };

    println!("array: {:?}", array.fields());
    let compiled = BytecodeCompiler::compile(&interpreter.vm.shared, array);

    for instruction in compiled.instructions {
        interpreter.execute_bytecode(instruction);
    }
}
