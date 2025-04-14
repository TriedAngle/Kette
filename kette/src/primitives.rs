use crate::{
    Array, ByteArray, Context, Map, Object, Parser, Quotation, SLOT_METHOD,
    StackFn, Tagged, Word,
};

pub fn add_primitives(ctx: &mut Context) {
    let words: &[(&str, &str, StackFn)] = &[
        // stack
        ("dup", "x -- x x", dup),
        ("2dup", "x y -- x y x y", dup2),
        ("3dup", "x y z -- x y z x y z", dup3),
        ("4dup", "x y z w -- x y z w x y z w", dup4),
        ("drop", "x -- ", drop),
        ("2drop", "x -- ", drop2),
        ("3drop", "x -- ", drop3),
        ("swap", "x y -- y x", swap),
        ("over", "x y -- x y x", over),
        ("rot", "x y z -- y z x", rot),
        ("-rot", "x y z -- z x y", rot_neg),
        ("dropd", "x y -- x", dropd),
        // fixnum
        ("fixnum+", "a b -- c", fixnum_add),
        ("fixnum-", "a b -- c", fixnum_sub),
        ("fixnum*", "a b -- c", fixnum_mul),
        ("fixnum/", "a b -- c", fixnum_div),
        ("fixnum>utf8", "num -- str", fixnum_to_string),
        ("fixnum=", "a b -- ?", fixnum_eq),
        ("fixnum!=", "a b -- ?", fixnum_neq),
        ("fixnum>", "a b -- ?", fixnum_gt),
        ("fixnum<", "a b -- ?", fixnum_lt),
        ("fixnum>=", "a b -- ?", fixnum_geq),
        ("fixnum<=", "a b -- ?", fixnum_leq),
        ("fixnum?", "obj -- ?", fixnum_is),
        ("2fixnum?", "obj1 obj2 -- ?", fixnum_is2),
        // general
        ("if", "? t-branch f-branch -- t/f-called", iff),
        ("not", " ? -- !? ", not),
        ("array>quotation", "array -- q", array_to_quotation),
        ("has-tag?", "word tag -- f", has_tag),
        // objects
        ("send-self", "..a obj name -- ..b", send_self),
        ("send-super", "..a obj name -- ..b", send_super),
        ("(clone)", "a -- b", clone),
        ("(new)", "map -- obj", new_from_prototype),
        ("(new-boa)", "..a map -- obj", new_by_order_of_args),
        ("set-prototype", "obj map -- ", set_prototype),
        ("<array>", "n -- array", create_array),
        ("<bytearray>", "n -- bytearray", create_bytearray),
        ("resize-array", "array n -- new", resize_array),
        ("resize-bytearray", "bytearray n -- new", resize_bytearray),
        ("(array-resize-push)", "array obj -- array", array_push),
        ("obj>map", "obj -- map", get_map),
        ("obj>ptr", "obj -- ptr", get_ptr),
        ("ptr>obj", "obj -- ptr", ptr_to_obj),
        ("ref-eq?", "obj -- ptr", ref_eq),
        ("slot", "obj n -- value", get_slot),
        ("set-slot", "value obj n -- ", set_slot),
        ("get-u8", "obj n -- u8", get_u8),
        ("set-u8", "u8 obj n -- ", set_u8),
        // vm
        ("(call)", "..a q -- ..b", call),
        ("(print)", "str -- ", print_utf8),
        ("(println)", "str -- ", println_utf8),
        ("@print-stack", " -- ", print_stack),
        (">r", "a -- ", data_to_retain),
        ("r>", " -- a", retain_to_data),
        ("r@", " -- ", retain_copy),
        ("depth", " -- n", data_depth),
        ("rdepth", " -- n", retain_depth),
        ("namestack|insert", "k v -- old-k old-v", namestack_push),
        ("namestack|find", "k -- k v", namestack_lookup),
        ("namestack|delete", "k -- k v", namestack_remove),
        ("get-frame", " -- stackframe", get_current_frame),
        ("push-handler", "handler -- ", push_handler),
        ("pop-handler", " -- handler", pop_handler),
        ("throw", "error -- ", throw),
        ("unwind-to-frame", " frame -- ", unwind_to_frame),
        ("panic", "message -- ", error_panic),
        ("(special)", "idx -- special", get_special),
        // parser
        ("@read-next", " -- str", read_next),
        ("@read-until", "end -- str", read_until),
        ("@parse-int", "str -- int/f", parse_int),
        ("@parse-until", "end/f -- array/f", parse_until),
        ("@skip-whitespace", " -- ", skip_whitespace),
    ];

    let syntaxes: &[(&str, StackFn)] =
        &[("@:", parse_syntax), ("f", push_false), ("t", push_true)];

    for &(name, _stack_effect, fun) in words {
        let fun = Tagged::from_fn(fun);
        let word =
            ctx.gc
                .allocate_primitive_word(name, Tagged::null(), fun, false);
        ctx.namestack_push(word, Tagged::null());
    }

    for &(name, fun) in syntaxes {
        let fun = Tagged::from_fn(fun);
        let word =
            ctx.gc
                .allocate_primitive_word(name, Tagged::null(), fun, true);
        ctx.namestack_push(word, Tagged::null());
    }
}

fn push_false(ctx: &mut Context) {
    ctx.push(Tagged::ffalse());
    array_push(ctx);
}

fn push_true(ctx: &mut Context) {
    ctx.push(ctx.gc.specials.true_obj);
    array_push(ctx);
}

fn parse_syntax(ctx: &mut Context) {
    let name = ctx.read_next();
    let res = ctx.parse_until(Some(";"));
    ctx.push(res);
    array_to_quotation(ctx);
    let quot = ctx.pop();
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
    ctx.push(res);
}

fn skip_whitespace(ctx: &mut Context) {
    ctx.skip_whitespace();
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

fn has_tag(ctx: &mut Context) {
    let tag = ctx.pop();
    let word_obj = ctx.pop();
    let word = word_obj.to_ptr() as *const Word;
    let has = unsafe { (*word).has_tag(tag) };
    push_bool(ctx, has);
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

fn new_from_prototype(ctx: &mut Context) {
    let map_obj = ctx.pop();
    let map_ptr = map_obj.to_ptr() as *mut Map;

    unsafe {
        let prototype = (*map_ptr).prototype;

        if prototype == Tagged::null() {
            let obj = ctx.gc.allocate_object(map_obj);
            ctx.push(obj);
        } else {
            let cloned = ctx.gc.clone(prototype);
            ctx.push(cloned);
        }
    }
}

fn new_by_order_of_args(ctx: &mut Context) {
    let map_obj = ctx.pop();
    let map_ptr = map_obj.to_ptr() as *mut Map;

    let obj = ctx.gc.allocate_object(map_obj);
    let obj_ptr = obj.to_ptr();

    unsafe {
        let data_slots = (*map_ptr).data_slots.to_int() as usize;

        for i in (0..data_slots).rev() {
            let value = ctx.pop();
            (*obj_ptr).set_slot(i, value);
        }
    }

    ctx.push(obj);
}

fn set_prototype(ctx: &mut Context) {
    let map_obj = ctx.pop();
    let instance = ctx.pop();

    let map_ptr = map_obj.to_ptr() as *mut Map;

    unsafe {
        (*map_ptr).prototype = instance;
    }
}

fn create_array(ctx: &mut Context) {
    let len_obj = ctx.pop();
    let len = len_obj.to_int();

    let array = ctx.gc.allocate_array(len as usize);
    ctx.push(array);
}

fn create_bytearray(ctx: &mut Context) {
    let len_obj = ctx.pop();
    let len = len_obj.to_int();

    let bytearray = ctx.gc.allocate_bytearray(len as usize);
    ctx.push(bytearray);
}

fn resize_array(ctx: &mut Context) {
    let len_obj = ctx.pop();
    let array = ctx.pop();
    let len = len_obj.to_int();
    let new = ctx.gc.resize_array(array, len as usize);
    ctx.push(new)
}

fn resize_bytearray(ctx: &mut Context) {
    let len_obj = ctx.pop();
    let bytearray = ctx.pop();
    let len = len_obj.to_int();
    let new = ctx.gc.resize_bytearray(bytearray, len as usize);
    ctx.push(new)
}

fn array_push(ctx: &mut Context) {
    let obj = ctx.pop();
    let mut array = ctx.pop();
    let mut array_ptr = array.to_ptr() as *mut Array;
    if unsafe { (*array_ptr).is_full() } {
        let new_capacity = unsafe { (*array_ptr).capacity() * 2 };
        let new = ctx.gc.resize_array(array, new_capacity);
        array = new;
        array_ptr = new.to_ptr() as _;
    }
    unsafe { (*array_ptr).push(obj) };
    ctx.push(array);
}

fn get_map(ctx: &mut Context) {
    let obj = ctx.pop();
    if obj.is_int() {
        let map = ctx.gc.specials.fixnum_map;
        ctx.push(map);
        return;
    }
    if obj.is_false() {
        let map = ctx.gc.specials.false_map;
        ctx.push(map);
        return;
    }
    let obj_ptr = obj.to_ptr();
    let header = unsafe { (*obj_ptr).header };
    let map = header.get_map();
    let map_obj = Tagged::from_ptr(map as _);
    ctx.push(map_obj);
}

fn get_ptr(ctx: &mut Context) {
    let obj = ctx.pop();
    let ptr = obj.to_ptr();
    let int = Tagged::from_int(ptr as _);
    ctx.push(int)
}

fn ptr_to_obj(ctx: &mut Context) {
    let ptr_obj = ctx.pop();
    let ptr_int = ptr_obj.to_int();
    let ptr = ptr_int as *mut Object;
    let obj = Tagged::from_ptr(ptr);
    ctx.push(obj);
}

fn ref_eq(ctx: &mut Context) {
    let obj2 = ctx.pop();
    let obj1 = ctx.pop();
    let is = obj2 == obj1;
    push_bool(ctx, is);
}

fn get_slot(ctx: &mut Context) {
    let n_obj = ctx.pop();
    let obj = ctx.pop();
    let n = n_obj.to_int();
    let obj_ptr = obj.to_ptr();
    let value = unsafe { (*obj_ptr).get_slot(n as usize) };
    ctx.push(value);
}

fn set_slot(ctx: &mut Context) {
    let n_obj = ctx.pop();
    let obj = ctx.pop();
    let value = ctx.pop();
    let n = n_obj.to_int();
    let obj_ptr = obj.to_ptr();
    unsafe { (*obj_ptr).set_slot(n as usize, value) };
}

fn get_u8(ctx: &mut Context) {
    let n_obj = ctx.pop();
    let obj = ctx.pop();
    let n = n_obj.to_int();
    let obj_ptr = obj.to_ptr() as *mut ByteArray;
    let u8 = unsafe { (*obj_ptr).get_byte(n as usize) };
    let fixnum = Tagged::from_int(u8 as i64);
    ctx.push(fixnum);
}

fn set_u8(ctx: &mut Context) {
    let n_obj = ctx.pop();
    let obj = ctx.pop();
    let value_obj = ctx.pop();
    let n = n_obj.to_int();
    let obj_ptr = obj.to_ptr() as *mut ByteArray;
    let value = value_obj.to_int();
    unsafe { (*obj_ptr).set_byte(n as usize, value as u8) };
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

fn fixnum_neq(ctx: &mut Context) {
    let (a, b) = pop2num(ctx);
    let res = a != b;
    push_bool(ctx, res);
}

fn fixnum_gt(ctx: &mut Context) {
    let (a, b) = pop2num(ctx);
    let res = a > b;
    push_bool(ctx, res);
}

fn fixnum_lt(ctx: &mut Context) {
    let (a, b) = pop2num(ctx);
    let res = a < b;
    push_bool(ctx, res);
}

fn fixnum_geq(ctx: &mut Context) {
    let (a, b) = pop2num(ctx);
    let res = a >= b;
    push_bool(ctx, res);
}

fn fixnum_leq(ctx: &mut Context) {
    let (a, b) = pop2num(ctx);
    let res = a <= b;
    push_bool(ctx, res);
}

fn fixnum_is(ctx: &mut Context) {
    let obj = ctx.pop();
    let is = obj.is_int();
    push_bool(ctx, is);
}

fn fixnum_is2(ctx: &mut Context) {
    let obj2 = ctx.pop();
    let obj1 = ctx.pop();
    let is2 = obj2.is_int();
    let is1 = obj1.is_int();
    let is = is2 && is1;
    push_bool(ctx, is);
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

fn not(ctx: &mut Context) {
    let b = ctx.pop();
    let is = b.is_false();
    push_bool(ctx, is);
}

fn print_stack(ctx: &mut Context) {
    ctx.print_stack();
}

fn dup(ctx: &mut Context) {
    let obj = ctx.pop();
    ctx.push(obj);
    ctx.push(obj);
}

fn dup2(ctx: &mut Context) {
    let obj2 = ctx.pop();
    let obj1 = ctx.pop();
    ctx.push(obj1);
    ctx.push(obj2);
    ctx.push(obj1);
    ctx.push(obj2);
}

fn dup3(ctx: &mut Context) {
    let obj3 = ctx.pop();
    let obj2 = ctx.pop();
    let obj1 = ctx.pop();
    ctx.push(obj1);
    ctx.push(obj2);
    ctx.push(obj3);
    ctx.push(obj1);
    ctx.push(obj2);
    ctx.push(obj3);
}

fn dup4(ctx: &mut Context) {
    let obj4 = ctx.pop();
    let obj3 = ctx.pop();
    let obj2 = ctx.pop();
    let obj1 = ctx.pop();
    ctx.push(obj1);
    ctx.push(obj2);
    ctx.push(obj3);
    ctx.push(obj4);
    ctx.push(obj1);
    ctx.push(obj2);
    ctx.push(obj3);
    ctx.push(obj4);
}

fn drop(ctx: &mut Context) {
    let _ = ctx.pop();
}

fn drop2(ctx: &mut Context) {
    let _ = ctx.pop();
    let _ = ctx.pop();
}

fn drop3(ctx: &mut Context) {
    let _ = ctx.pop();
    let _ = ctx.pop();
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

// x y z -- z x y
fn rot_neg(ctx: &mut Context) {
    let z = ctx.pop();
    let y = ctx.pop();
    let x = ctx.pop();
    ctx.push(z);
    ctx.push(x);
    ctx.push(y);
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

fn retain_copy(ctx: &mut Context) {
    let val = ctx.retain_pop();
    ctx.retain_push(val);
    ctx.push(val);
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

fn get_current_frame(ctx: &mut Context) {
    let frame = ctx.get_current_frame();
    ctx.push(frame);
}

fn push_handler(ctx: &mut Context) {
    let handler = ctx.pop();
    ctx.push_handler(handler);
}

fn pop_handler(ctx: &mut Context) {
    let handler = ctx.pop_handler();
    ctx.push(handler);
}

fn throw(ctx: &mut Context) {
    let exception = ctx.pop();
    ctx.throw(exception);
}

fn unwind_to_frame(ctx: &mut Context) {
    let frame = ctx.pop();
    ctx.unwind_to_frame(frame);
}

fn error_panic(ctx: &mut Context) {
    let message = ctx.pop();

    if message.is_false() {
        println!("PANIC: <no message>");
    } else {
        let message_ptr = message.to_ptr() as *const ByteArray;
        let message_str = unsafe { (*message_ptr).as_str() };
        println!("PANIC: {}", message_str);
    }

    println!("Stack trace:");

    let frame = ctx.get_current_frame();
    if frame.is_false() {
        println!("  <callstack empty or unavailable>");
    } else {
        // TODO: implement this
        println!("  <callstack empty or unavailable>");
        // let mut depth = 0;
        // let mut current_frame = ctx.call.current;
        // let mut frames = Vec::new();
        //
        // while current_frame > ctx.call.start {
        //     unsafe { current_frame = current_frame.sub(1) };
        //     let frame_obj = unsafe { *current_frame };
        //
        //     if !frame_obj.is_false() && !frame_obj.is_int() {
        //         frames.push(frame_obj);
        //     }
        // }
        //
        // for frame in frames.iter().rev() {
        //     print_frame(ctx, *frame, depth);
        //     depth += 1;
        // }
    }

    // Terminate execution with panic
    panic!("VM execution terminated due to panic");
}

fn get_special(ctx: &mut Context) {
    let idx_obj = ctx.pop();
    let idx = idx_obj.to_int();
    let obj = ctx.gc.specials.get_nth(idx as usize);
    ctx.push(obj);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        ByteArray, CodeHeap, Context, ContextConfig, GarbageCollector, Handler,
        Object, SLOT_CONST_DATA, SLOT_PARENT, Tagged, Word, primitives,
    };
    use parking_lot::Mutex;
    use std::sync::Arc;

    fn setup_context() -> Context {
        let code_heap = Arc::new(Mutex::new(CodeHeap::new()));
        let config = ContextConfig {
            data_size: 100,
            retian_size: 100,
            name_size: 100,
            call_size: 100,
            handler_size: 100,
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
        let mut ctx = setup_context();

        let parent_map = ctx.gc.create_map("ParentClass", &[]);

        let child_map = ctx.gc.create_map("ChildClass", &[]);
        let child_obj = ctx.gc.allocate_object(child_map);

        ctx.gc.push_slot(
            child_map,
            "parent",
            SLOT_PARENT,
            parent_map,
            Tagged::ffalse(),
        );

        let parent_greeting = ctx.gc.allocate_string("Hello from parent");
        let parent_method_body = vec![parent_greeting];
        let parent_method = ctx.gc.allocate_quotation(&parent_method_body);

        ctx.gc.push_slot(
            parent_map,
            "greet",
            SLOT_METHOD,
            parent_method,
            Tagged::ffalse(),
        );

        let child_greeting = ctx.gc.allocate_string("Hello from child");
        let child_method_body = vec![child_greeting];
        let child_method = ctx.gc.allocate_quotation(&child_method_body);

        ctx.gc.push_slot(
            child_map,
            "greet",
            SLOT_METHOD,
            child_method,
            Tagged::ffalse(),
        );

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

    #[test]
    fn test_new_primitives() {
        let mut ctx = setup_context();

        let person_map = ctx.gc.create_map(
            "Person",
            &[
                (
                    "name",
                    SLOT_CONST_DATA,
                    Tagged::from_int(0),
                    Tagged::ffalse(),
                ),
                (
                    "age",
                    SLOT_CONST_DATA,
                    Tagged::from_int(1),
                    Tagged::ffalse(),
                ),
            ],
        );

        let name = ctx.gc.allocate_string("John");
        ctx.push(name);
        ctx.push(Tagged::from_int(30));

        ctx.push(person_map);
        new_by_order_of_args(&mut ctx);

        let person1 = ctx.pop();
        let person1_ptr = person1.to_ptr();

        unsafe {
            let name_slot = (*person1_ptr).get_slot(0);
            let name_ptr = name_slot.to_ptr() as *const ByteArray;
            assert_eq!((*name_ptr).as_str(), "John");

            let age_slot = (*person1_ptr).get_slot(1);
            assert_eq!(age_slot.to_int(), 30);
        }

        ctx.push(person1);
        ctx.push(person_map);
        set_prototype(&mut ctx);

        ctx.push(person_map);
        new_from_prototype(&mut ctx);

        let person2 = ctx.pop();
        let person2_ptr = person2.to_ptr();

        assert!(person1.to_ptr() != person2.to_ptr());

        unsafe {
            let name_slot = (*person2_ptr).get_slot(0);
            let name_ptr = name_slot.to_ptr() as *const ByteArray;
            assert_eq!((*name_ptr).as_str(), "John");

            let age_slot = (*person2_ptr).get_slot(1);
            assert_eq!(age_slot.to_int(), 30);
        }
    }

    #[test]
    fn test_empty_map_always_has_prototype() {
        let mut gc = GarbageCollector::new();

        let empty_map = gc.create_map("EmptyClass", &[]);

        unsafe {
            let map_ptr = empty_map.to_ptr() as *mut Map;
            let prototype = (*map_ptr).prototype;

            assert!(!prototype.is_false());
            assert!(prototype != Tagged::null());

            let proto_ptr = prototype.to_ptr();
            let proto_map_ptr = (*proto_ptr).header.get_map();

            assert_eq!(proto_map_ptr as *mut Object, empty_map.to_ptr());
        }

        let mut ctx = setup_context();
        ctx.push(empty_map);
        new_from_prototype(&mut ctx);

        let instance = ctx.pop();

        unsafe {
            let instance_ptr = instance.to_ptr();
            let instance_map_ptr = (*instance_ptr).header.get_map();

            assert!(instance.to_ptr() != empty_map.to_ptr());
            assert_eq!(instance_map_ptr as *mut Object, empty_map.to_ptr());
        }
    }

    #[test]
    fn test_map_with_default_values() {
        let mut gc = GarbageCollector::new();

        let default_name = gc.allocate_string("Default Name");
        let default_age = Tagged::from_int(25);

        let person_map = gc.create_map(
            "Person",
            &[
                ("name", SLOT_CONST_DATA, Tagged::from_int(0), default_name),
                ("age", SLOT_CONST_DATA, Tagged::from_int(1), default_age),
            ],
        );

        unsafe {
            let map_ptr = person_map.to_ptr() as *mut Map;
            let prototype = (*map_ptr).prototype;
            assert!(!prototype.is_false());

            let proto_ptr = prototype.to_ptr();

            let name_slot = (*proto_ptr).get_slot(0);
            let name_ptr = name_slot.to_ptr() as *const ByteArray;
            assert_eq!((*name_ptr).as_str(), "Default Name");
            let age_slot = (*proto_ptr).get_slot(1);
            assert_eq!(age_slot.to_int(), 25);
        }

        let mut ctx = setup_context();
        ctx.push(person_map);
        new_from_prototype(&mut ctx);

        let person = ctx.pop();

        unsafe {
            let person_ptr = person.to_ptr();
            let name_slot = (*person_ptr).get_slot(0);
            let name_ptr = name_slot.to_ptr() as *const ByteArray;
            assert_eq!((*name_ptr).as_str(), "Default Name");

            let age_slot = (*person_ptr).get_slot(1);
            assert_eq!(age_slot.to_int(), 25);
        }
    }

    #[test]
    fn test_array_creation_and_resizing() {
        let mut ctx = setup_context();

        ctx.push(Tagged::from_int(5));
        primitives::create_array(&mut ctx);

        let array = ctx.pop();
        assert!(!array.is_false());

        let array_ptr = array.to_ptr() as *const crate::Array;
        unsafe {
            assert_eq!((*array_ptr).capacity(), 5);

            for i in 0..5 {
                assert_eq!((*array_ptr).get(i), Tagged::null());
            }
        }

        ctx.push(array);
        ctx.push(Tagged::from_int(8));
        primitives::resize_array(&mut ctx);

        let resized_array = ctx.pop();
        assert!(!resized_array.is_false());

        let resized_ptr = resized_array.to_ptr() as *const crate::Array;
        unsafe {
            assert_eq!((*resized_ptr).capacity(), 8);

            for i in 0..5 {
                assert_eq!((*resized_ptr).get(i), Tagged::null());
            }
            for i in 5..8 {
                assert_eq!((*resized_ptr).get(i), Tagged::null());
            }
        }

        ctx.push(resized_array);
        ctx.push(Tagged::from_int(3));
        primitives::resize_array(&mut ctx);

        let shrunk_array = ctx.pop();
        assert!(!shrunk_array.is_false());

        let shrunk_ptr = shrunk_array.to_ptr() as *const crate::Array;
        unsafe {
            assert_eq!((*shrunk_ptr).capacity(), 3);

            for i in 0..3 {
                assert_eq!((*shrunk_ptr).get(i), Tagged::null());
            }
        }
    }

    #[test]
    fn test_bytearray_creation_and_resizing() {
        let mut ctx = setup_context();

        ctx.push(Tagged::from_int(5));
        primitives::create_bytearray(&mut ctx);

        let bytearray = ctx.pop();
        assert!(!bytearray.is_false());

        let bytearray_ptr = bytearray.to_ptr() as *const crate::ByteArray;
        unsafe {
            assert_eq!((*bytearray_ptr).len(), 5);

            for i in 0..5 {
                assert_eq!((*bytearray_ptr).get_byte(i), 0);
            }
        }

        ctx.push(bytearray);
        ctx.push(Tagged::from_int(8));
        primitives::resize_bytearray(&mut ctx);

        let resized_bytearray = ctx.pop();
        assert!(!resized_bytearray.is_false());

        let resized_ptr = resized_bytearray.to_ptr() as *const crate::ByteArray;
        unsafe {
            assert_eq!((*resized_ptr).len(), 8);

            for i in 0..5 {
                assert_eq!((*resized_ptr).get_byte(i), 0);
            }
            for i in 5..8 {
                assert_eq!((*resized_ptr).get_byte(i), 0);
            }
        }

        ctx.push(resized_bytearray);
        ctx.push(Tagged::from_int(3));
        primitives::resize_bytearray(&mut ctx);

        let shrunk_bytearray = ctx.pop();
        assert!(!shrunk_bytearray.is_false());

        let shrunk_ptr = shrunk_bytearray.to_ptr() as *const crate::ByteArray;
        unsafe {
            assert_eq!((*shrunk_ptr).len(), 3);

            for i in 0..3 {
                assert_eq!((*shrunk_ptr).get_byte(i), 0);
            }
        }
    }

    #[test]
    fn test_get_set_slot() {
        let mut ctx = setup_context();

        let map = ctx.gc.create_map("TestObject", &[]);
        let obj = ctx.gc.allocate_object(map);

        let values = [
            Tagged::from_int(42),
            ctx.gc.allocate_string("hello"),
            ctx.gc.specials.true_obj,
        ];

        for (i, value) in values.iter().enumerate() {
            ctx.push(*value);
            ctx.push(obj);
            ctx.push(Tagged::from_int(i as i64));
            primitives::set_slot(&mut ctx);

            ctx.push(obj);
            ctx.push(Tagged::from_int(i as i64));
            primitives::get_slot(&mut ctx);

            let result = ctx.pop();
            match i {
                0 => assert_eq!(result.to_int(), 42),
                1 => {
                    let str_ptr = result.to_ptr() as *const crate::ByteArray;
                    let string = unsafe { (*str_ptr).as_str() };
                    assert_eq!(string, "hello");
                }
                2 => assert_eq!(result, ctx.gc.specials.true_obj),
                _ => panic!("Unexpected index"),
            }
        }

        ctx.push(Tagged::from_int(99));
        ctx.push(obj);
        ctx.push(Tagged::from_int(0));
        primitives::set_slot(&mut ctx);

        ctx.push(obj);
        ctx.push(Tagged::from_int(0));
        primitives::get_slot(&mut ctx);

        let result = ctx.pop();
        assert_eq!(result.to_int(), 99);
    }

    #[test]
    fn test_get_set_u8() {
        let mut ctx = setup_context();

        ctx.push(Tagged::from_int(10));
        primitives::create_bytearray(&mut ctx);
        let bytearray = ctx.pop();

        let test_bytes = [65, 66, 67, 68, 69];

        for (i, &byte) in test_bytes.iter().enumerate() {
            ctx.push(Tagged::from_int(byte as i64));
            ctx.push(bytearray);
            ctx.push(Tagged::from_int(i as i64));
            primitives::set_u8(&mut ctx);
        }

        for (i, &expected) in test_bytes.iter().enumerate() {
            ctx.push(bytearray);
            ctx.push(Tagged::from_int(i as i64));
            primitives::get_u8(&mut ctx);

            let result = ctx.pop();
            assert_eq!(result.to_int(), expected as i64);
        }

        let bytearray_ptr = bytearray.to_ptr() as *const crate::ByteArray;
        let string = unsafe { (*bytearray_ptr).as_str() };
        assert_eq!(string, "ABCDE\0\0\0\0");

        ctx.push(Tagged::from_int(90));
        ctx.push(bytearray);
        ctx.push(Tagged::from_int(0));
        primitives::set_u8(&mut ctx);

        ctx.push(bytearray);
        ctx.push(Tagged::from_int(0));
        primitives::get_u8(&mut ctx);

        let result = ctx.pop();
        assert_eq!(result.to_int(), 90);
    }

    #[test]
    fn test_array_operations_integration() {
        let mut ctx = setup_context();

        ctx.push(Tagged::from_int(3));
        primitives::create_array(&mut ctx);
        let array = ctx.pop();

        for i in 0..3 {
            ctx.push(Tagged::from_int(i * 10));
            ctx.push(array);
            ctx.push(Tagged::from_int(i + 2));
            primitives::set_slot(&mut ctx);
        }

        for i in 0..3 {
            ctx.push(array);
            ctx.push(Tagged::from_int(i + 2));
            primitives::get_slot(&mut ctx);

            let result = ctx.pop();
            assert_eq!(result.to_int(), i * 10);
        }

        ctx.push(array);
        ctx.push(Tagged::from_int(5));
        primitives::resize_array(&mut ctx);
        let resized = ctx.pop();

        for i in 0..3 {
            ctx.push(resized);
            ctx.push(Tagged::from_int(i + 2));
            primitives::get_slot(&mut ctx);

            let result = ctx.pop();
            assert_eq!(result.to_int(), i * 10);
        }

        for i in 3..5 {
            ctx.push(Tagged::from_int(i * 10));
            ctx.push(resized);
            ctx.push(Tagged::from_int(i + 2));
            primitives::set_slot(&mut ctx);
        }

        for i in 0..5 {
            ctx.push(resized);
            ctx.push(Tagged::from_int(i + 2));
            primitives::get_slot(&mut ctx);

            let result = ctx.pop();
            assert_eq!(result.to_int(), i * 10);
        }
    }

    #[test]
    fn test_bytearray_as_string() {
        let mut ctx = setup_context();

        let text = "Hello World";
        ctx.push(Tagged::from_int((text.len() + 1) as i64));
        primitives::create_bytearray(&mut ctx);
        let bytearray = ctx.pop();

        for (i, byte) in text.bytes().enumerate() {
            ctx.push(Tagged::from_int(byte as i64));
            ctx.push(bytearray);
            ctx.push(Tagged::from_int(i as i64));
            primitives::set_u8(&mut ctx);
        }

        for (i, expected) in text.bytes().enumerate() {
            ctx.push(bytearray);
            ctx.push(Tagged::from_int(i as i64));
            primitives::get_u8(&mut ctx);

            let result = ctx.pop();
            assert_eq!(result.to_int(), expected as i64);
        }

        let bytearray_ptr = bytearray.to_ptr() as *const crate::ByteArray;
        let string = unsafe { (*bytearray_ptr).as_str() };
        assert_eq!(string, text);
    }

    #[test]
    fn test_edge_cases() {
        let mut ctx = setup_context();

        ctx.push(Tagged::from_int(0));
        primitives::create_array(&mut ctx);
        let empty_array = ctx.pop();

        ctx.push(Tagged::from_int(0));
        primitives::create_bytearray(&mut ctx);
        let empty_bytearray = ctx.pop();

        unsafe {
            let array_ptr = empty_array.to_ptr() as *const crate::Array;
            let bytearray_ptr =
                empty_bytearray.to_ptr() as *const crate::ByteArray;

            assert_eq!((*array_ptr).capacity(), 0);
            assert_eq!((*bytearray_ptr).len(), 0);
        }

        ctx.push(Tagged::from_int(5));
        primitives::create_array(&mut ctx);
        let array = ctx.pop();

        ctx.push(array);
        ctx.push(Tagged::from_int(0));
        primitives::resize_array(&mut ctx);
        let resized_array = ctx.pop();

        unsafe {
            let array_ptr = resized_array.to_ptr() as *const crate::Array;
            assert_eq!((*array_ptr).capacity(), 0);
        }
    }

    #[test]
    fn test_push_pop_handler() {
        let mut ctx = setup_context();

        let frame = ctx.get_current_frame();
        let handler = create_test_handler(&mut ctx, frame, Tagged::ffalse());

        ctx.push(handler);
        let lookup_name = ctx.gc.allocate_string("push-handler");
        let push_handler_word = ctx.lookup(lookup_name).0;
        ctx.execute_word(push_handler_word.to_ptr() as *const Word);

        let lookup_name = ctx.gc.allocate_string("pop-handler");
        let pop_handler_word = ctx.lookup(lookup_name).0;
        ctx.execute_word(pop_handler_word.to_ptr() as *const Word);

        let popped = ctx.pop();
        assert_eq!(popped, handler);
    }

    fn create_test_handler(
        ctx: &mut Context,
        frame: Tagged,
        tty: Tagged,
    ) -> Tagged {
        let lookup_name = ctx.gc.allocate_string("println-utf8");
        let handler_body = vec![
            ctx.gc.allocate_string("Handler executed"),
            ctx.lookup(lookup_name).0,
        ];
        let handler_quot = ctx.gc.allocate_quotation(&handler_body);

        let handler_obj = ctx.gc.allocate_object(ctx.gc.specials.handler_map);
        let handler_ptr = handler_obj.to_ptr() as *mut Handler;

        unsafe {
            (*handler_ptr).frame = frame;
            (*handler_ptr).tty = tty;
            (*handler_ptr).handler = handler_quot;
        }

        handler_obj
    }

    #[test]
    fn test_handler_stack_management() {
        let mut ctx = setup_context();

        let frame = ctx.get_current_frame();
        let handler1 = create_test_handler(&mut ctx, frame, Tagged::ffalse());
        ctx.push_handler(handler1);

        let ba_map = ctx.gc.specials.bytearray_map;
        let handler2 = create_test_handler(&mut ctx, frame, ba_map);
        ctx.push_handler(handler2);

        let popped2 = ctx.pop_handler();
        assert_eq!(popped2, handler2);

        let popped1 = ctx.pop_handler();
        assert_eq!(popped1, handler1);

        let popped_empty = ctx.pop_handler();
        assert_eq!(popped_empty, Tagged::ffalse());
    }

    #[test]
    fn test_frame_and_unwinding() {
        let mut ctx = setup_context();

        let dummy_frame = ctx.gc.allocate_object(ctx.gc.specials.object_map);

        let current_call_ptr = ctx.call.current;
        let entry_ptr = current_call_ptr as *mut Tagged;
        unsafe {
            *entry_ptr = dummy_frame;
        }
        ctx.call.increment(1);

        let lookup_name = ctx.gc.allocate_string("get-frame");
        let get_frame_word = ctx.lookup(lookup_name).0;
        ctx.execute_word(get_frame_word.to_ptr() as *const Word);
        let frame1 = ctx.pop();

        assert_eq!(frame1, dummy_frame);

        let dummy_frame2 = ctx.gc.allocate_object(ctx.gc.specials.object_map);

        let current_call_ptr = ctx.call.current;
        let entry_ptr = current_call_ptr as *mut Tagged;
        unsafe {
            *entry_ptr = dummy_frame2;
        }
        ctx.call.increment(1);

        ctx.execute_word(get_frame_word.to_ptr() as *const Word);
        let frame2 = ctx.pop();

        assert_ne!(frame1, frame2);
        assert_eq!(frame2, dummy_frame2);

        ctx.push(frame1);
        let lookup_name = ctx.gc.allocate_string("unwind-to-frame");
        let unwind_word = ctx.lookup(lookup_name).0;
        ctx.execute_word(unwind_word.to_ptr() as *const Word);

        ctx.execute_word(get_frame_word.to_ptr() as *const Word);
        let frame_after_unwind = ctx.pop();

        assert_eq!(frame_after_unwind, frame1);
    }

    #[test]
    fn test_is_type_match() {
        let mut ctx = setup_context();

        let parent_map = ctx.create_map("ParentType", &[]);
        let child_map = ctx.create_map(
            "ChildType",
            &[("Parent", SLOT_PARENT, parent_map, Tagged::ffalse())],
        );

        let parent_obj = ctx.gc.allocate_object(parent_map);
        let child_obj = ctx.gc.allocate_object(child_map);
        let other_obj = ctx.gc.allocate_object(ctx.gc.specials.object_map);

        assert!(ctx.is_instance_of(parent_obj, parent_map));
        assert!(ctx.is_instance_of(child_obj, child_map));

        assert!(ctx.is_instance_of(child_obj, parent_map));

        assert!(!ctx.is_instance_of(parent_obj, child_map));
        assert!(!ctx.is_instance_of(other_obj, parent_map));
        assert!(!ctx.is_instance_of(other_obj, child_map));

        assert!(!ctx.is_instance_of(parent_obj, Tagged::ffalse()));
    }
}
