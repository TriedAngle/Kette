use kette::{HeapCreateInfo, VM, VMCreateInfo};

fn main() {
    let _vm = VM::new(VMCreateInfo {
        image: None,
        heap: HeapCreateInfo {
            ..Default::default()
        },
    });

    println!("Hello, world!");
}
