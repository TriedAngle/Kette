use kette::{
    Block, ExecutionState, ExecutionStateInfo, HeapCreateInfo, Instruction, Interpreter, Parser,
    ThreadProxy, ThreadShared, ThreadState, VM, VMCreateInfo, VMThread, primitive_index,
};

const CODE: &str = r#"
5 77 fixnum+ fixnum>utf8-bytes bytearray-println
"#;

fn demo_compiled() -> Block {
    Block {
        instructions: vec![
            Instruction::PushFixnum { value: 10 },
            Instruction::PushFixnum { value: 60 },
            Instruction::PushFixnum { value: 0 }, // TODO: implement stack object, this is a dummy
            Instruction::SendPrimitive {
                id: primitive_index("swap"),
            },
            Instruction::PushFixnum { value: 20 },
            Instruction::SendPrimitive {
                id: primitive_index("fixnum+"),
            },
            Instruction::SendPrimitive {
                id: primitive_index("fixnum>utf8-bytes"),
            },
            Instruction::SendPrimitive {
                id: primitive_index("bytearray-println"),
            },
            Instruction::SendPrimitive {
                id: primitive_index("fixnum>utf8-bytes"),
            },
            Instruction::SendPrimitive {
                id: primitive_index("bytearray-println"),
            },
        ],
    }
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
    let heap = main_proxy.shared.heap.create_proxy();

    let state = ExecutionState::new(&ExecutionStateInfo {
        stack_size: 128,
        return_stack_size: 128,
    });

    // TODO: make create function for this.
    let main_thread = VMThread::new_main();
    let thread_proxy = ThreadProxy(main_thread.inner);

    let proxy = vm.new_proxy();

    let mut interpreter = Interpreter::new(proxy, thread_proxy, heap, state);

    for instruction in demo_compiled().instructions {
        interpreter.execute_bytecode(instruction);
    }
}
