use kette::PRELOAD;
use kette::VM;
use std::io::{self, Write};

fn main() {
    let mut vm = VM::new();
    vm.init();

    // accessing vm special objects example: let-me-cook 1 slot 8 + get^ ^object 0 slot utf8. -> prints "world"

    unsafe {
        let quot = vm.compile_string(PRELOAD);
        vm.execute_quotation(quot.as_quotation());
    }

    let testing = r#"
            420 3 t <array> array-push array.

            { $[ 2 neg ] 3 4 } array.

            t f 69 \ while* 4array array.
            

            (): stevejones x y ;

            s" good at" s" programming" stevejones tuple-boa
            [ 0 slot utf8. ] [ 1 slot utf8. ] bi

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
        }
    }

    vm.deinit();
}
