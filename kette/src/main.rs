#![allow(unused)]

use kette::VM;

fn main() {
    let mut vm = VM::new();
    vm.init();

    let input = "420 690 fixnum+ fixnum. 3 [ 2 fixnum* ] call fixnum.";
    unsafe {
        let quot = vm.parse_string(input);
        vm.print_quotation(quot);
        vm.execute_quotation(quot.as_quotation());
    }
}
