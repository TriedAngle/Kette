use kette::VM;
use std::io::{self, Write};

fn main() {
    let mut vm = VM::new();
    vm.init();

    // accessing vm special objects example: let-me-cook 1 slot 8 + get^ ^object 0 slot utf8. -> prints "world"

    let preload = r#"
        : + ( a b -- c ) fixnum+ ;
        : - ( a b -- c ) fixnum- ;
        : . ( a -- ) fixnum. ;
        : / ( a -- ) fixnum/ ;
        : = ( a b -- ? ) fixnum= ;
        : % ( a b -- c ) fixnum% ;
        : > ( a b -- ? ) fixnum> ;
        : >= ( a b -- ? ) fixnum>= ;

        : 2dup ( a b -- a b a b ) dup [ dupd swap ] dip ; 
        : 2dip ( ... a b q -- ... a b ... ) swap [ dip ] dip ;
        : 2keep ( ... a b q -- ... a b ) [ 2dup ] dip 2dip ;
        : 2drop ( a b -- ) drop drop ;

        : ^object ( ptr -- obj ) 0 slot ;

        : when ( ... ? q -- ... ) swap [ call ] [ drop ] if ;
        : unless ( ... ? q -- ... ) swap [ drop ] [ call ] if ;

        : loop ( ... q -- ... ) [ call ] keep swap [ loop ] when ;

        : while ( ... cond body -- ... ) [ [ call ] keep ] dip rot 
            [ [ dropd call ] 2keep while ] [ 2drop ] if ;
    "#;

    unsafe {
        let quot = vm.compile_string(preload);
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
