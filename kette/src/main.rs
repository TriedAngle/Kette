use kette::VM;

fn main() {
    let mut vm = VM::new();
    vm.init();

    let input = r#"
        : + ( a b -- c ) fixnum+ ;
        : - ( a b -- c ) fixnum- ;
        : . ( a -- ) fixnum. ;
        : / ( a -- ) fixnum/ ;
        : = ( a b -- ? ) fixnum= ;
        : % ( a b -- c ) fixnum% ;
        : > ( a b -- ? ) fixnum> ;
        : >= ( a b -- ? ) fixnum>= ;
        : -1 ( a -- a-1 ) 1 - ;
        
        : n| ( a n -- ? ) % 0 = ;
        : !n| ( a n -- ? ) n| not ;

        : when ( ... ? q -- ... ) swap [ call ] [ drop ] if ;

        : fizzbuzz ( num -- ) 
            dup 15 n| [ s" FizzBuzz" utf8. ] [
                dup 3 n| [ s" Fizz" utf8. ] when 
                dup 5 n| [ s" Buzz" utf8. ] when
            ] if

            dup [ 3 !n| ] keep 5 !n| and [ dup . ] when
            dup 0 > [ -1 fizzbuzz ] when ;

        15 fizzbuzz
    "#;
    unsafe {
        let quot = vm.compile_string(input);
        // vm.print_quotation(quot);
        vm.execute_quotation(quot.as_quotation());
    }
}
