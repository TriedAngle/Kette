use crate::{ExecutionResult, PrimitiveContext, StringObject, Value};

pub fn parent(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let p = ctx.vm.specials().string_traits;
    ctx.outputs[0] = p.into();
    ExecutionResult::Normal
}

pub fn size(ctx: &mut PrimitiveContext) -> ExecutionResult {
    // SAFETY: receiver must be valid string
    let s = unsafe { ctx.receiver.cast::<StringObject>() };
    let size = s.as_bytes().len();
    // SAFETY: this is safe
    ctx.outputs[0] = unsafe { Value::from_usize(size).as_handle_unchecked() };
    ExecutionResult::Normal
}

pub fn string_to_bytearray(ctx: &mut PrimitiveContext) -> ExecutionResult {
    // SAFETY: receiver must be valid string
    let s = unsafe { ctx.receiver.cast::<StringObject>() };
    ctx.outputs[0] = s.value.into();
    ExecutionResult::Normal
}

pub fn string_to_message(ctx: &mut PrimitiveContext) -> ExecutionResult {
    // SAFETY: receiver must be valid string
    let s = unsafe { ctx.receiver.cast::<StringObject>() };
    let message = ctx.vm.intern_message(s, ctx.heap);
    ctx.outputs[0] = message.into();
    ExecutionResult::Normal
}
