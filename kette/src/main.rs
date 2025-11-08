use kette::{HeapCreateInfo, VM, VMCreateInfo};

fn main() {
    let vm = VM::new(VMCreateInfo {
        image: None,
        heap: HeapCreateInfo {
            ..Default::default()
        },
    });

    println!("Hello, world!");
}
