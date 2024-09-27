use kette::VM;
use std::io::{self, Write};

fn main() {
    let mut vm = VM::new();
    vm.init();

    // accessing vm special objects example: let-me-cook 1 slot 8 + get^ ^object 0 slot utf8. -> prints "world"

    unsafe {
        let stage0 = vm.compile_source_file("std/core/stage-0.ktt");
        vm.execute_quotation(stage0.as_quotation());

        let stage1 = vm.compile_source_file("std/core/stage-1.ktt");
        vm.execute_quotation(stage1.as_quotation());
    }

    let testing = r#"
        
        
        "#;
    unsafe {
        let quot = vm.compile_string(testing);
        vm.execute_quotation(quot.as_quotation());
    }

    let mut step_mode = false;

    loop {
        io::stdout().flush().unwrap();
        print!("IN: ");
        io::stdout().flush().unwrap();
        let mut input = String::new();
        io::stdin()
            .read_line(&mut input)
            .expect("Failed to read line");
        if input == "S\n" {
            // \x13 is Ctrl+S in ASCII
            step_mode = !step_mode;
            println!(
                "Step mode {}",
                if step_mode {
                    "activated"
                } else {
                    "deactivated"
                }
            );
            continue;
        }

        if input == "E\n" {
            break;
        }

        unsafe {
            let quot = vm.compile_string(&input);
            vm.execute_quotation(quot.as_quotation());
            let ctx = vm.ctx();
            let stack2 = ctx.data_array;
            let len2 = ctx.len();
            vm.print_array(stack2, len2);
        }
    }

    vm.deinit();
}
