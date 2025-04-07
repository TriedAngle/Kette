use crate::{ByteArray, Context, ParseStackFn, Parser, StackFn, Tagged};

pub fn add_primitives(ctx: &mut Context) {
    let words: &[(&str, &str, StackFn)] = &[
        ("fixnum+", "a b -- c", fixnum_add),
        ("fixnum-", "a b -- c", fixnum_sub),
        ("fixnum*", "a b -- c", fixnum_mul),
        ("fixnum/", "a b -- c", fixnum_div),
        ("fixnum>utf8", "num -- str", fixnum_to_string),
        ("print-utf8", "str -- ", print_utf8),
        ("println-utf8", "str -- ", println_utf8),
        ("dup", "x -- x x", dup),
        ("drop", "x -- ", drop),
        ("swap", "x y -- y x", swap),
        ("over", "x y -- x y x", over),
        ("rot", "x y z -- y z x", rot),
        ("dropd", "x y -- x", dropd),
        // Stack transfer primitives
        (">r", "a -- ", data_to_retain),
        ("r>", " -- a", retain_to_data),
        // Depth primitives
        ("depth", " -- n", data_depth),
        ("rdepth", " -- n", retain_depth),
    ];

    let syntaxes: &[(&str, ParseStackFn)] = &[("[", parse_quotation)];

    for &(name, _stack_effect, fun) in words {
        let fun = Tagged::from_fn(fun);
        let word = ctx
            .gc
            .allocate_primitive_word(name, Tagged::null(), fun, false);
        ctx.namestack_push(word, Tagged::null());
    }

    for &(name, fun) in syntaxes {
        let fun = Tagged::from_parse_fn(fun);
        let word = ctx
            .gc
            .allocate_primitive_word(name, Tagged::null(), fun, true);
        ctx.namestack_push(word, Tagged::null());
    }
}

fn parse_quotation(ctx: &mut Context, parser: &mut Parser) {
    let res = parser.parse_until(ctx, Some("]"));
    let quot = ctx.gc.allocate_quotation(&res);
    ctx.push(quot);
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

fn pop_bytearray(ctx: &mut Context) -> *mut ByteArray {
    let obj = ctx.pop();
    let ptr = obj.to_ptr() as *mut ByteArray;
    ptr
}

pub fn iff(_ctx: &mut Context) {
    panic!("this shouldn't be called");
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
        let elements = (data_ptr as usize - data_start as usize) / std::mem::size_of::<Tagged>();
        elements as i64
    };
    push_num(ctx, depth);
}

fn retain_depth(ctx: &mut Context) {
    let depth = {
        let retain_ptr = ctx.retain.current;
        let retain_start = ctx.retain.start;
        let elements =
            (retain_ptr as usize - retain_start as usize) / std::mem::size_of::<Tagged>();
        elements as i64
    };
    push_num(ctx, depth);
}

#[cfg(test)]
mod tests {
    use crate::{ByteArray, CodeHeap, Context, ContextConfig, Tagged, Word, primitives};
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
}
