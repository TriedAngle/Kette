use crate::{ExecutionResult, Message, PrimitiveContext};

pub fn parent(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let p = ctx.vm.specials().message_traits;
    ctx.outputs[0] = p.into();
    ExecutionResult::Normal
}

pub fn name(ctx: &mut PrimitiveContext) -> ExecutionResult {
    // SAFETY: safe
    let message = unsafe { ctx.receiver.cast::<Message>() };
    let name = message.value;

    ctx.outputs[0] = name.into();
    ExecutionResult::Normal
}
