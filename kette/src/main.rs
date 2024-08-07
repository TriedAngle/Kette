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
        method: to-string ( obj -- string )
        
        type: shape x y ;
        m: shape to-string drop s" shape" ;

        type: cat name ;
        m: cat to-string [ s" cat with name " ] dip name>> bytearray-concat ;

        !/
        420 69 shape boa to-string utf8.
        s" Steve" cat boa to-string utf8.
        !/

        !/ type: box < shape width height !/

        !/ 
        5 { 
            { [ 0 = ] [ drop s" zero" . 2 ] } 
            { [ 0 < ] [ drop s" negative" .  3 ] } 
            { [ 0 > ] [ drop s" positive" .  3 ] } 
        } match
        !/
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
            let v = &mut vm as *mut VM;
            let stack = (*v).allocate_array_from_slice(&vm.stack);
            vm.print_array(stack);
        }
    }

    vm.deinit();
}
