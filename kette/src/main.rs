use kette::{
    Block, ExecutionState, ExecutionStateInfo, HeapCreateInfo, Instruction, Interpreter, Parser,
    ThreadProxy, ThreadShared, ThreadState, VM, VMCreateInfo, VMThread,
};

const CODE: &str = r#"
5 77 fixnum+ fixnum>utf8-bytes bytearray-println
"#;

fn demo_compiled() -> Block {
    Block {
        instructions: vec![
            Instruction::PushFixnum { value: 10 },
            Instruction::PushFixnum { value: 20 },
            Instruction::SendNamed { message: "fixnum+" },
            Instruction::SendNamed {
                message: "fixnum>utf8-bytes",
            },
            Instruction::SendNamed {
                message: "bytearray-println",
            },
        ],
    }
}

fn main() {
    let vm = VM::new(VMCreateInfo {
        image: None,
        heap: HeapCreateInfo {
            ..Default::default()
        },
    });

    let main_proxy = vm.new_proxy();
    let heap = main_proxy.shared.heap.create_proxy();

    let state = ExecutionState::new(&ExecutionStateInfo {
        stack_size: 128,
        return_stack_size: 128,
    });

    let main_thread = VMThread::new_main();
    let thread_proxy = ThreadProxy(main_thread.inner);

    let proxy = vm.new_proxy();

    let interpreter = Interpreter::new(proxy, thread_proxy, heap, state);

    // let mut parser = Parser::new(CODE.as_bytes());
    //
    // let mut parsed = Vec::new();
    // while let Some(parse) = parser.parse_next() {
    //     // match parse {
    //
    //     // }
    // }
}
