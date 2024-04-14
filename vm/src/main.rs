#![allow(dead_code, unused)]

use vm::{objects::Integer, VM};

fn main() {
    let mut vm = VM::new();
    let str = vm.alloc_rust_string("hello");

    let a = vm.alloc_int(666);
    let b = vm.alloc_int(33);
    vm.push(a);
    vm.push(b);
    let pb = vm.pop().deref_mut::<Integer>().value;
    let pa = vm.pop().deref_mut::<Integer>().value;
    assert_eq!(pb, 33);
    assert_eq!(pa, 666);

    println!("Hello, world!");
}
