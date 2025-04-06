use crate::{ByteArray, Context, Tagged};

fn pop1num(ctx: &mut Context) -> i64 {
    let obj = ctx.pop();
    let num = obj.to_int();
    num
}

fn pop2num(ctx: &mut Context) -> (i64, i64) {
    let obj_a = ctx.pop();
    let obj_b = ctx.pop();
    let a = obj_a.to_int();
    let b = obj_b.to_int();
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
