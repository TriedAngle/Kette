use kette::{
    ExecutionState, ExecutionStateCreateInfo, Executor, HeapCreateInfo, Parser, VM, VMCreateInfo,
    VMThread, VMThreadProxy,
};

const CODE: &str = r#"
5 77 fixnum+ fixnum>utf8-bytes bytearray-println
"#;

fn main() {
    let vm = VM::new(VMCreateInfo {
        image: None,
        heap: HeapCreateInfo {
            ..Default::default()
        },
    });

    let main_proxy = vm.new_proxy();
    let heap = main_proxy.shared.heap.create_proxy();

    let state = ExecutionState::new(&ExecutionStateCreateInfo {
        stack_size: 128,
        return_stack_size: 128,
    });

    let main_thread = VMThread::new_main(main_proxy);
    let main_thread_proxy = VMThreadProxy(main_thread.inner.clone());

    let _executor = Executor::new(main_thread_proxy, heap, state);

    let mut parser = Parser::new(CODE.as_bytes());

    // let mut parsed = Vec::new();
    // while let Some(parse) = parser.parse_next() {
    //     match parse {
    //
    //     }
    // }
}
