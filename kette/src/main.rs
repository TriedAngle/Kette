use kette::{
    Block, ExecutionState, ExecutionStateInfo, HeapCreateInfo, HeapProxy,
    Instruction, Interpreter, ThreadProxy, VM, VMCreateInfo, VMProxy, VMThread,
    primitive_index,
};

const _CODE: &str = r#"
5 77 fixnum+ fixnum>utf8-bytes bytearray-println
"#;

fn demo_compiled(vm: &VMProxy, _heap: &mut HeapProxy) -> Block {
    Block {
        #[rustfmt::skip]
        instructions: vec![
            Instruction::PushFixnum { value: 10 },
            Instruction::PushFixnum { value: 60 },
            Instruction::PushValue {
                value: vm.specials().stack_object.as_value(),
            },
            Instruction::SendNamed { message: "swap" },
            Instruction::PushFixnum { value: 20 },
            Instruction::SendNamed { message: "fixnum+" },
            Instruction::SendNamed { message: "fixnum>utf8-bytes" },
            Instruction::SendNamed { message: "bytearray-println" },
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
    let mut heap = main_proxy.shared.heap.create_proxy();

    let state = ExecutionState::new(&ExecutionStateInfo {
        stack_size: 128,
        return_stack_size: 128,
    });

    // TODO: make create function for this.
    let main_thread = VMThread::new_main();
    let thread_proxy = ThreadProxy(main_thread.inner);

    let proxy = vm.new_proxy();

    let compiled = demo_compiled(&main_proxy, &mut heap);

    let mut interpreter = Interpreter::new(proxy, thread_proxy, heap, state);

    for instruction in compiled.instructions {
        interpreter.execute_bytecode(instruction);
    }
}
