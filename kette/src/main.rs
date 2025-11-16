use kette::{ExecutionState, ExecutionStateCreateInfo, HeapCreateInfo, VM, VMCreateInfo};

const _CODE: &str = r#"
5 77 fixnum+ fixnum>utf8-bytes bytearray-println
"#;

fn main() {
    let vm = VM::new(VMCreateInfo {
        image: None,
        heap: HeapCreateInfo {
            ..Default::default()
        },
    });

    let _main_proxy = vm.new_proxy();
    let _main_state = ExecutionState::new(&ExecutionStateCreateInfo {
        stack_size: 128,
        return_stack_size: 128,
    });
}
