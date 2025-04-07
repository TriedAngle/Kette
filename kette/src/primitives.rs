use crate::{
    Array, ByteArray, Context, ParseStackFn, Parser, Quotation, SLOT_METHOD,
    StackFn, Tagged, Word,
};

pub fn add_primitives(ctx: &mut Context) {
    let words: &[(&str, &str, StackFn)] = &[
        // stack
        ("dup", "x -- x x", dup),
        ("drop", "x -- ", drop),
        ("swap", "x y -- y x", swap),
        ("over", "x y -- x y x", over),
        ("rot", "x y z -- y z x", rot),
        ("dropd", "x y -- x", dropd),
        // fixnum
        ("fixnum+", "a b -- c", fixnum_add),
        ("fixnum-", "a b -- c", fixnum_sub),
        ("fixnum*", "a b -- c", fixnum_mul),
        ("fixnum/", "a b -- c", fixnum_div),
        ("fixnum>utf8", "num -- str", fixnum_to_string),
        ("fixnum=", "a b -- ?", fixnum_eq),
        // general
        ("if", "? t-branch f-branch -- t/f-called", iff),
        ("array>quotation", "array -- q", array_to_quotation),
        ("send-self", "..a obj name -- ..b", send_self),
        ("send-super", "..a obj name -- ..b", send_super),
        // vm
        ("(call)", "..a q -- ..b", call),
        ("(clone)", "a -- b", clone),
        ("print-utf8", "str -- ", print_utf8),
        ("println-utf8", "str -- ", println_utf8),
        (">r", "a -- ", data_to_retain),
        ("r>", " -- a", retain_to_data),
        ("depth", " -- n", data_depth),
        ("rdepth", " -- n", retain_depth),
        ("namestack|insert", "k v -- old-k old-v", namestack_push),
        ("namestack|find", "k -- k v", namestack_lookup),
        ("namestack|delete", "k -- k v", namestack_remove),
        // parser
        ("@read-next", " -- str", read_next),
        ("@read-until", "end -- str", read_until),
        ("@parse-int", "str -- int/f", parse_int),
        ("@parse-word", "str -- word/f", parse_word),
        ("@parse-until", "end/f -- array/f", parse_until),
    ];

    let syntaxes: &[(&str, ParseStackFn)] = &[
        ("[", parse_quotation),
        ("@:", parse_syntax),
        ("f", push_false),
        ("t", push_true),
    ];

    for &(name, _stack_effect, fun) in words {
        let fun = Tagged::from_fn(fun);
        let word =
            ctx.gc
                .allocate_primitive_word(name, Tagged::null(), fun, false);
        ctx.namestack_push(word, Tagged::null());
    }

    for &(name, fun) in syntaxes {
        let fun = Tagged::from_parse_fn(fun);
        let word =
            ctx.gc
                .allocate_primitive_word(name, Tagged::null(), fun, true);
        ctx.namestack_push(word, Tagged::null());
    }
}

fn parse_quotation(ctx: &mut Context, parser: &mut Parser) {
    let res = parser.parse_until(ctx, Some("]"));
    let quot = ctx.gc.allocate_quotation(&res);
    ctx.push(quot);
}

fn push_false(ctx: &mut Context, _parser: &mut Parser) {
    ctx.push(Tagged::ffalse());
}

fn push_true(ctx: &mut Context, _parser: &mut Parser) {
    ctx.push(ctx.gc.specials.true_obj);
}

fn parse_syntax(ctx: &mut Context, parser: &mut Parser) {
    let name = parser.read_next(ctx);
    let res = parser.parse_until(ctx, Some(";"));
    let quot = ctx.gc.allocate_quotation(&res);
    let tags = ctx.gc.allocate_array(1);
    let word = ctx.gc.allocate_object(ctx.gc.specials.word_map);

    let tags_ptr = tags.to_ptr() as *mut Array;
    let word_ptr = word.to_ptr() as *mut Word;

    unsafe {
        (*tags_ptr).set(0, ctx.gc.specials.parser_tag);

        (*word_ptr).name = name;
        (*word_ptr).effect = Tagged::ffalse();
        (*word_ptr).tags = tags;
        (*word_ptr).body = quot;
    }

    ctx.namestack_push(word, Tagged::ffalse());
}

fn read_next(ctx: &mut Context) {
    let next = ctx.read_next();
    ctx.push(next);
}

fn parse_int(ctx: &mut Context) {
    let value = ctx.pop();
    if let Some(int) = Parser::parse_int(value) {
        ctx.push(int);
    } else {
        ctx.push(Tagged::ffalse())
    }
}

fn parse_word(ctx: &mut Context) {
    let value = ctx.pop();
    let parser = ctx.gc.specials.parser.to_ptr() as *mut Parser;
    if let Some(word) = unsafe { (*parser).parse_word(ctx, value) } {
        ctx.push(word);
    } else {
        ctx.push(Tagged::ffalse())
    }
}

fn read_until(ctx: &mut Context) {
    let end_obj = ctx.pop();
    let end_ptr = end_obj.to_ptr() as *const ByteArray;
    let end_str = unsafe { (*end_ptr).as_str() };

    let word = ctx.read_until(end_str);
    ctx.push(word);
}

fn parse_until(ctx: &mut Context) {
    let delimiter_obj = ctx.pop();

    let delimiter = if delimiter_obj.is_false() {
        None
    } else {
        let ba = delimiter_obj.to_ptr() as *const ByteArray;
        let s = unsafe { (*ba).as_str() };
        Some(s)
    };

    let res = ctx.parse_until(delimiter);

    let array = ctx.gc.allocate_array(res.len());
    let array_ptr = array.to_ptr() as *mut Array;
    for (i, item) in res.iter().enumerate() {
        unsafe {
            (*array_ptr).set(i, *item);
        }
    }

    ctx.push(array);
}

fn call(ctx: &mut Context) {
    let quot_obj = ctx.pop();
    let quot = quot_obj.to_ptr() as *const Quotation;
    ctx.execute(quot);
}

fn clone(ctx: &mut Context) {
    let value = ctx.pop();
    let cloned = ctx.gc.clone(value);
    ctx.push(cloned);
}

fn pop1num(ctx: &mut Context) -> i64 {
    let obj = ctx.pop();
    let num = obj.to_int();
    num
}

fn pop2num(ctx: &mut Context) -> (i64, i64) {
    let obj_b = ctx.pop();
    let obj_a = ctx.pop();
    let b = obj_b.to_int();
    let a = obj_a.to_int();
    (a, b)
}

fn push_num(ctx: &mut Context, num: i64) {
    let tagged = Tagged::from_int(num);
    ctx.push(tagged);
}

fn push_bool(ctx: &mut Context, val: bool) {
    if val {
        ctx.push(ctx.gc.specials.true_obj);
    } else {
        ctx.push(Tagged::ffalse());
    }
}

fn pop_bytearray(ctx: &mut Context) -> *mut ByteArray {
    let obj = ctx.pop();
    let ptr = obj.to_ptr() as *mut ByteArray;
    ptr
}

pub fn iff(ctx: &mut Context) {
    let false_branch_obj = ctx.pop();
    let true_branch_obj = ctx.pop();
    let condition = ctx.pop();
    if condition.is_false() {
        let false_branch = false_branch_obj.to_ptr() as _;
        ctx.execute(false_branch);
    } else {
        let true_branch = true_branch_obj.to_ptr() as _;
        ctx.execute(true_branch);
    }
}

fn array_to_quotation(ctx: &mut Context) {
    let array = ctx.pop();
    let quotation = ctx.gc.allocate_object(ctx.gc.specials.quotation_map);
    let quot_ptr = quotation.to_ptr() as *mut Quotation;

    unsafe { (*quot_ptr).body = array };

    ctx.push(quotation);
}

fn get_bytearray_str(tagged: Tagged) -> &'static str {
    let ba_ptr = tagged.to_ptr() as *const ByteArray;
    unsafe { (*ba_ptr).as_str() }
}

fn find_and_execute_method(
    ctx: &mut Context,
    obj: Tagged,
    msg_name: &str,
    use_super: bool,
) {
    let obj_ptr = obj.to_ptr();
    let map_ptr = unsafe { (*obj_ptr).header.get_map() };

    let method_slot = if use_super {
        unsafe { (*map_ptr).find_super(msg_name, Some(SLOT_METHOD)) }
    } else {
        unsafe { (*map_ptr).find_slot(msg_name, Some(SLOT_METHOD)) }
    };

    if let Some(slot) = method_slot {
        let method = unsafe { (*slot).value };

        ctx.push(obj);

        ctx.push(method);

        call(ctx);
    } else {
        ctx.push(Tagged::ffalse());
    }
}

pub fn send_self(ctx: &mut Context) {
    let msg = ctx.pop();
    let obj = ctx.pop();

    let msg_name = get_bytearray_str(msg);

    find_and_execute_method(ctx, obj, msg_name, false);
}

pub fn send_super(ctx: &mut Context) {
    let msg = ctx.pop();
    let obj = ctx.pop();

    let msg_name = get_bytearray_str(msg);

    find_and_execute_method(ctx, obj, msg_name, true);
}

fn fixnum_add(ctx: &mut Context) {
    let (a, b) = pop2num(ctx);
    let c = a + b;
    push_num(ctx, c);
}

fn fixnum_sub(ctx: &mut Context) {
    let (a, b) = pop2num(ctx);
    let c = a - b;
    push_num(ctx, c);
}

fn fixnum_mul(ctx: &mut Context) {
    let (a, b) = pop2num(ctx);
    let c = a * b;
    push_num(ctx, c);
}

fn fixnum_div(ctx: &mut Context) {
    let (a, b) = pop2num(ctx);
    let c = a / b;
    push_num(ctx, c);
}

fn fixnum_eq(ctx: &mut Context) {
    let (a, b) = pop2num(ctx);
    let res = a == b;
    push_bool(ctx, res);
}

fn fixnum_to_string(ctx: &mut Context) {
    let num = pop1num(ctx);
    let s = num.to_string();
    let ba = ctx.gc.allocate_string(&s);
    ctx.push(ba);
}

fn println_utf8(ctx: &mut Context) {
    let ba = pop_bytearray(ctx);
    let s = unsafe { (*ba).as_str() };
    println!("{s}");
}

fn print_utf8(ctx: &mut Context) {
    let ba = pop_bytearray(ctx);
    let s = unsafe { (*ba).as_str() };
    print!("{s}");
}

fn dup(ctx: &mut Context) {
    let obj = ctx.pop();
    ctx.push(obj);
    ctx.push(obj);
}

fn drop(ctx: &mut Context) {
    let _ = ctx.pop();
}

fn swap(ctx: &mut Context) {
    let y = ctx.pop();
    let x = ctx.pop();
    ctx.push(y);
    ctx.push(x);
}

fn over(ctx: &mut Context) {
    let y = ctx.pop();
    let x = ctx.pop();
    ctx.push(x);
    ctx.push(y);
    ctx.push(x);
}

fn rot(ctx: &mut Context) {
    let z = ctx.pop();
    let y = ctx.pop();
    let x = ctx.pop();
    ctx.push(y);
    ctx.push(z);
    ctx.push(x);
}

fn dropd(ctx: &mut Context) {
    let a = ctx.pop();
    let _ = ctx.pop();
    ctx.push(a);
}

fn data_to_retain(ctx: &mut Context) {
    ctx.data_retain();
}

fn retain_to_data(ctx: &mut Context) {
    ctx.retain_data();
}

fn data_depth(ctx: &mut Context) {
    let depth = {
        let data_ptr = ctx.data.current;
        let data_start = ctx.data.start;
        let elements = (data_ptr as usize - data_start as usize)
            / std::mem::size_of::<Tagged>();
        elements as i64
    };
    push_num(ctx, depth);
}

fn retain_depth(ctx: &mut Context) {
    let depth = {
        let retain_ptr = ctx.retain.current;
        let retain_start = ctx.retain.start;
        let elements = (retain_ptr as usize - retain_start as usize)
            / std::mem::size_of::<Tagged>();
        elements as i64
    };
    push_num(ctx, depth);
}

fn namestack_push(ctx: &mut Context) {
    let value = ctx.pop();
    let key = ctx.pop();
    let (old_key, old_value) = ctx.namestack_push(key, value);
    ctx.push(old_key);
    ctx.push(old_value);
}

fn namestack_lookup(ctx: &mut Context) {
    let key = ctx.pop();
    let (key, value) = ctx.lookup(key);
    ctx.push(key);
    ctx.push(value);
}

fn namestack_remove(ctx: &mut Context) {
    let key = ctx.pop();
    let (key, value) = ctx.namestack_remove(key);
    ctx.push(key);
    ctx.push(value);
}

#[cfg(test)]
mod tests {
    use crate::{
        ByteArray, CodeHeap, Context, ContextConfig, Tagged, Word, primitives,
    };
    use parking_lot::Mutex;
    use std::sync::Arc;

    fn setup_context() -> Context {
        let code_heap = Arc::new(Mutex::new(CodeHeap::new()));
        let config = ContextConfig {
            data_size: 100,
            retian_size: 100,
            name_size: 100,
        };
        let mut ctx = Context::new(&config, code_heap);
        primitives::add_primitives(&mut ctx);
        ctx
    }

    #[test]
    fn test_fixnum_arithmetic() {
        let mut ctx = setup_context();

        ctx.push(Tagged::from_int(5));
        ctx.push(Tagged::from_int(3));
        primitives::fixnum_add(&mut ctx);
        assert_eq!(ctx.pop().to_int(), 8);

        ctx.push(Tagged::from_int(10));
        ctx.push(Tagged::from_int(4));
        primitives::fixnum_sub(&mut ctx);
        assert_eq!(ctx.pop().to_int(), 6);

        ctx.push(Tagged::from_int(6));
        ctx.push(Tagged::from_int(7));
        primitives::fixnum_mul(&mut ctx);
        assert_eq!(ctx.pop().to_int(), 42);

        ctx.push(Tagged::from_int(20));
        ctx.push(Tagged::from_int(5));
        primitives::fixnum_div(&mut ctx);
        assert_eq!(ctx.pop().to_int(), 4);
    }

    #[test]
    fn test_string_conversion() {
        let mut ctx = setup_context();

        ctx.push(Tagged::from_int(42));
        primitives::fixnum_to_string(&mut ctx);

        let result = ctx.pop();
        let str_ptr = result.to_ptr() as *const crate::ByteArray;
        let string = unsafe { (*str_ptr).as_str() };

        assert_eq!(string, "42");
    }

    #[test]
    fn test_stack_manipulation() {
        let mut ctx = setup_context();

        ctx.push(Tagged::from_int(42));
        primitives::dup(&mut ctx);
        assert_eq!(ctx.pop().to_int(), 42);
        assert_eq!(ctx.pop().to_int(), 42);

        ctx.push(Tagged::from_int(42));
        primitives::drop(&mut ctx);
        assert_eq!(ctx.data.current, ctx.data.start);

        ctx.push(Tagged::from_int(1));
        ctx.push(Tagged::from_int(2));
        primitives::swap(&mut ctx);
        assert_eq!(ctx.pop().to_int(), 1);
        assert_eq!(ctx.pop().to_int(), 2);

        ctx.push(Tagged::from_int(1));
        ctx.push(Tagged::from_int(2));
        primitives::over(&mut ctx);
        assert_eq!(ctx.pop().to_int(), 1);
        assert_eq!(ctx.pop().to_int(), 2);
        assert_eq!(ctx.pop().to_int(), 1);

        ctx.push(Tagged::from_int(1));
        ctx.push(Tagged::from_int(2));
        ctx.push(Tagged::from_int(3));
        primitives::rot(&mut ctx);
        assert_eq!(ctx.pop().to_int(), 1);
        assert_eq!(ctx.pop().to_int(), 3);
        assert_eq!(ctx.pop().to_int(), 2);

        ctx.push(Tagged::from_int(1));
        ctx.push(Tagged::from_int(2));
        primitives::dropd(&mut ctx);
        assert_eq!(ctx.pop().to_int(), 2);
        assert_eq!(ctx.data.current, ctx.data.start);
    }

    #[test]
    fn test_retain_transfer() {
        let mut ctx = setup_context();

        ctx.push(Tagged::from_int(42));
        primitives::data_to_retain(&mut ctx);
        assert_eq!(ctx.data.current, ctx.data.start);

        primitives::retain_to_data(&mut ctx);
        assert_eq!(ctx.pop().to_int(), 42);
        assert_eq!(ctx.retain.current, ctx.retain.start);
    }

    #[test]
    fn test_depth_primitives() {
        let mut ctx = setup_context();

        ctx.push(Tagged::from_int(1));
        ctx.push(Tagged::from_int(2));
        ctx.push(Tagged::from_int(3));
        primitives::data_depth(&mut ctx);
        assert_eq!(ctx.pop().to_int(), 3);

        ctx.retain_push(Tagged::from_int(1));
        ctx.retain_push(Tagged::from_int(2));
        primitives::retain_depth(&mut ctx);
        assert_eq!(ctx.pop().to_int(), 2);
    }

    #[test]
    fn test_execution_with_primitives() {
        let mut ctx = setup_context();

        let items = vec![Tagged::from_int(5), Tagged::from_int(3)];

        let quotation = ctx.gc.allocate_quotation(&items);

        ctx.push(quotation);
        ctx.execute(quotation.to_ptr() as *const crate::Quotation);

        let word = ctx.gc.allocate_string("fixnum+");
        let (add_word, _) = ctx.lookup(word);
        let word = add_word.to_ptr() as *mut Word;
        let word_name = unsafe { (*word).name.to_ptr() as *mut ByteArray };
        assert_eq!(unsafe { (*word_name).as_str() }, "fixnum+");

        ctx.execute_word(add_word.to_ptr() as *const crate::Word);

        assert_eq!(ctx.pop().to_int(), 8);
    }

    #[test]
    fn test_send_methods() {
        use crate::{
            ByteArray, CodeHeap, Context, ContextConfig, SLOT_METHOD,
            SLOT_PARENT,
        };
        use parking_lot::Mutex;
        use std::sync::Arc;

        let code_heap = Arc::new(Mutex::new(CodeHeap::new()));
        let config = ContextConfig {
            data_size: 100,
            retian_size: 100,
            name_size: 100,
        };
        let mut ctx = Context::new(&config, code_heap);
        primitives::add_primitives(&mut ctx);

        let parent_map = ctx.gc.create_map("ParentClass", &[]);

        let child_map = ctx.gc.create_map("ChildClass", &[]);
        let child_obj = ctx.gc.allocate_object(child_map);

        ctx.gc
            .push_slot(child_map, "parent", SLOT_PARENT, parent_map);

        let parent_greeting = ctx.gc.allocate_string("Hello from parent");
        let parent_method_body = vec![parent_greeting];
        let parent_method = ctx.gc.allocate_quotation(&parent_method_body);

        ctx.gc
            .push_slot(parent_map, "greet", SLOT_METHOD, parent_method);

        let child_greeting = ctx.gc.allocate_string("Hello from child");
        let child_method_body = vec![child_greeting];
        let child_method = ctx.gc.allocate_quotation(&child_method_body);

        ctx.gc
            .push_slot(child_map, "greet", SLOT_METHOD, child_method);

        let method_name = ctx.gc.allocate_string("greet");
        ctx.push(child_obj);
        ctx.push(method_name);

        primitives::send_self(&mut ctx);

        let result = ctx.pop();
        assert!(!result.is_false());
        let result_str = unsafe {
            let ba_ptr = result.to_ptr() as *const ByteArray;
            (*ba_ptr).as_str()
        };
        assert_eq!(result_str, "Hello from child");

        let method_name = ctx.gc.allocate_string("greet");
        ctx.push(child_obj);
        ctx.push(method_name);

        primitives::send_super(&mut ctx);

        let result = ctx.pop();
        assert!(!result.is_false());
        let result_str = unsafe {
            let ba_ptr = result.to_ptr() as *const ByteArray;
            (*ba_ptr).as_str()
        };
        assert_eq!(result_str, "Hello from parent");

        let method_name = ctx.gc.allocate_string("non_existent");
        ctx.push(child_obj);
        ctx.push(method_name);

        primitives::send_self(&mut ctx);

        let result = ctx.pop();
        assert!(result.is_false());
    }
}
