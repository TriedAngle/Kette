use crate::{ByteArray, ExecutionResult, PrimitiveContext};

pub fn fixnum_to_utf8_bytes(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let _value = unsafe { ctx.receiver.as_fixnum::<i64>() };
    unimplemented!("TODO: allocate bytearray, maybe also cache this");
}

pub fn bytearray_print(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let ba = unsafe { ctx.receiver.cast::<ByteArray>() };
    let data = ba.as_bytes();
    let value = str::from_utf8(data).expect("valid utf8 encoding");
    print!("{}", value);
    ExecutionResult::Normal
}

pub fn bytearray_println(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let ba = unsafe { ctx.receiver.cast::<ByteArray>() };
    let data = ba.as_bytes();
    let value = str::from_utf8(data).expect("valid utf8 encoding");
    println!("{}", value);
    ExecutionResult::Normal
}
