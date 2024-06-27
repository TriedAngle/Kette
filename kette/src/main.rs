#![allow(unused)]

use kette::VM;

fn main() {
    let mut vm = VM::new();
    vm.init();
    vm.initialize_primitive_maps();
    vm.add_fixnum_primitives();

    let num1 = vm.allocate_fixnum(16);
    let num2 = vm.allocate_fixnum(5);
    vm.push(num1);
    vm.push(num2);

    let input = "420 690 fixnum+ fixnum.";
    vm.bind_input(input);

    unsafe {
        loop {
            vm.read_word();
            vm.dup();
            if vm.is_false() {
                break;
            }
            vm.dup();
            vm.try_parse_number();
            vm.dup();
            if vm.is_true() {
                vm.dropd();
                continue;
            } 

            vm.drop();
            let parsed_word = vm.pop();
            let word_str = (*parsed_word.as_byte_array()).as_str().unwrap();
            if let Some(word) = vm.words.get(word_str) {
                vm.execute_primitive(*word);
            }
        }
    }
}
