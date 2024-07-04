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
        : map>> ( obj -- map ) 1 neg slot ;
        : slots>> ( map -- slots ) 3 slot ;

        !/
        : lookup-slot ( name obj -- index ) 
            map>> slots>> <array-iter> [
                dup ?next dup 
                [ dup 0 slot pickd bytearray= [ 3 slot ] [ drop f ] if ] [ f ] if
                dup [ f ] [ drop t ] if
            ] loop 2dropd ;
        !/

        !: SLOT-CONSTANT 0
        !: SLOT_PARENT 1
        !: SLOT_DATA 2
        !: SLOT_ASSIGNMENT 3
        !: SLOT_METHOD 4
        !: SLOT_VARIABLE_DATA: 5
        !: SLOT_EMBEDDED_DATA: 6

        !/ TODO: write a find for sequences !/
        : lookup-slot ( name map -- slot )
            slots>> <array-iter> [
                dup ?next dup 
                [ dup 0 slot pickd bytearray= [ drop f ] unless ] [ t ] if
                dup [ f ] [ drop t ] if
            ] loop 2dropd dup t ref-eq? [ 2drop f ] when ;


        : set-slot-method ( word slot -- ) 
            [ SLOT_METHOD swap 1 set-slot ] 
            [ 2 set-slot ] 
            [ 0 swap 3 set-slot ] tri ;

        : slot-method (slot -- ) 
            dup 1 slot SLOT_METHOD fixnum= [ 2 slot ] [ drop f ] if ;

        @: builtin:
            @vm-next-token [ @vm-define-empty-global-word ] [ @vm-link-map ] bi
            define-push-word \ ;  @vm-skip-until drop t ;

        builtin: fixnum
        builtin:
        
        tuple: pos x y ;
        
        : x>> ( obj -- x ) dup \ x>> unbox 0 slot swap lookup-slot slot ;
        : x<< ( value obj -- ) dup \ x<< unbox 0 slot swap lookup-slot set-slot ;
        : >>x ( obj value -- obj ) dupd swap x<< ;


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
