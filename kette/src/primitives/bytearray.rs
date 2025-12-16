use crate::{ByteArray, ExecutionResult, PrimitiveContext};

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

pub fn parent(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let p = ctx.vm.specials().bytearray_traits;
    ctx.outputs[0] = p.into();
    ExecutionResult::Normal
}
