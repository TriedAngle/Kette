use crate::{ByteArray, ExecutionResult, PrimitiveContext};

pub fn fixnum_to_utf8_bytes(ctx: &mut PrimitiveContext) -> ExecutionResult {
    // SAFETY: receiver must be valid fixnum
    let value = unsafe { ctx.receiver.as_fixnum::<i64>() };
    let string = value.to_string();
    let ba = ctx.heap.allocate_bytearray_data(string.as_bytes());
    // SAFETY: no gc here
    ctx.outputs[0] = unsafe { ba.promote_to_handle().cast() };
    ExecutionResult::Normal
}

pub fn bytearray_print(ctx: &mut PrimitiveContext) -> ExecutionResult {
    // SAFETY: receiver must be valid Bytarray
    let ba = unsafe { ctx.receiver.cast::<ByteArray>() };
    let data = ba.as_bytes();
    let value = str::from_utf8(data).expect("valid utf8 encoding");
    print!("{}", value);
    ExecutionResult::Normal
}

pub fn bytearray_println(ctx: &mut PrimitiveContext) -> ExecutionResult {
    // SAFETY: receiver must be valid bytearray
    let ba = unsafe { ctx.receiver.cast::<ByteArray>() };
    let data = ba.as_bytes();
    let value = str::from_utf8(data).expect("valid utf8 encoding");
    println!("{}", value);
    ExecutionResult::Normal
}
