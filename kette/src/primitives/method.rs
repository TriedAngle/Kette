use crate::{ExecutionResult, Method, PrimitiveContext};

pub fn call(ctx: &mut PrimitiveContext) -> ExecutionResult {
    // SAFETY: this is safe
    let method = unsafe { ctx.receiver.cast::<Method>() };
    let receiver = ctx.inputs[0];
    ctx.interpreter.add_method(receiver, method);
    ExecutionResult::ActivationChanged
}
