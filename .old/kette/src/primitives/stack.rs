use super::outputs;
use crate::{ExecutionResult, PrimitiveContext, Value};

pub fn depth(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let depth = ctx.state.depth();
    // SAFETY: this is safe
    ctx.outputs[0] = unsafe { Value::from_usize(depth).as_handle_unchecked() };
    ExecutionResult::Normal
}

pub fn swap(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let y = ctx.receiver;
    let x = ctx.inputs[0];
    outputs(ctx, [y, x]);
    ExecutionResult::Normal
}

pub fn dup(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let x = ctx.receiver;
    outputs(ctx, [x, x]);
    ExecutionResult::Normal
}

pub fn dup2(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let x = ctx.inputs[0];
    let y = ctx.receiver;
    outputs(ctx, [x, y, x, y]);
    ExecutionResult::Normal
}

pub fn drop(_ctx: &mut PrimitiveContext) -> ExecutionResult {
    ExecutionResult::Normal
}

pub fn drop2(_ctx: &mut PrimitiveContext) -> ExecutionResult {
    ExecutionResult::Normal
}

pub fn drop3(_ctx: &mut PrimitiveContext) -> ExecutionResult {
    ExecutionResult::Normal
}

pub fn over(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let x = ctx.inputs[0];
    let y = ctx.receiver;
    outputs(ctx, [x, y, x]);
    ExecutionResult::Normal
}

pub fn pick(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let x = ctx.inputs[0];
    let y = ctx.inputs[1];
    let z = ctx.receiver;
    outputs(ctx, [x, y, z, x]);
    ExecutionResult::Normal
}

/// rotates top three elements backwards
pub fn rot(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let x = ctx.inputs[0];
    let y = ctx.inputs[1];
    let z = ctx.receiver;
    outputs(ctx, [y, z, x]);
    ExecutionResult::Normal
}

/// rotates top three elements forwards
pub fn neg_rot(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let x = ctx.inputs[0];
    let y = ctx.inputs[1];
    let z = ctx.receiver;
    outputs(ctx, [z, x, y]);
    ExecutionResult::Normal
}

pub fn spin(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let x = ctx.inputs[0];
    let y = ctx.inputs[1];
    let z = ctx.receiver;
    outputs(ctx, [z, y, x]);
    ExecutionResult::Normal
}

pub fn dupd(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let x = ctx.inputs[0];
    let y = ctx.receiver;
    outputs(ctx, [x, x, y]);
    ExecutionResult::Normal
}

pub fn dropd(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let y = ctx.receiver;
    outputs(ctx, [y]);
    ExecutionResult::Normal
}

pub fn dropd2(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let z = ctx.receiver;
    outputs(ctx, [z]);
    ExecutionResult::Normal
}

pub fn swapd(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let x = ctx.inputs[0];
    let y = ctx.inputs[1];
    let z = ctx.receiver;
    outputs(ctx, [y, x, z]);
    ExecutionResult::Normal
}
