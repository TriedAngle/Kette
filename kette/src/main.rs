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
    : -1 ( a -- a-1 ) 1 - ;
    : n| ( a n -- ? ) % 0 = ;
    : !n| ( a n -- ? ) n| not ;


    : fizzbuzz ( num -- )
        dup 15 n| [ s" FizzBuzz" utf8. ] [
            dup 3 n| [ s" Fizz" utf8. ] when
            dup 5 n| [ s" Buzz" utf8. ] when
        ] if

        dup [ 3 !n| ] [ 5 !n| ] bi and [ dup . ] when
        dup 0 > [ 1 -  fizzbuzz ] [ drop ] if ;
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
