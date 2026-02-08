use crate::{
    primitives::{bool_object, inputs, outputs},
    Allocator, ExecutionResult, PrimitiveContext, Quotation,
};

pub fn call(ctx: &mut PrimitiveContext) -> ExecutionResult {
    // SAFETY: this is safe
    let quotation = unsafe { ctx.receiver.cast::<Quotation>() };

    ctx.interpreter.add_quotation(quotation);
    ExecutionResult::ActivationChanged
}

// TODO: implement this
/// removes x, calls q, puts x again
/// x q -- x
pub fn dip(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let [x] = inputs(ctx);

    let q = ctx.receiver;
    ctx.state.push(q.into());
    outputs(ctx, [x]);

    let map = ctx.vm.shared.specials.dip_map;
    // SAFETY: this is safe
    let parent = unsafe { ctx.interpreter.context_unchecked().activation };
    let quotation = ctx.heap.allocate_quotation(map, parent);

    ctx.interpreter.add_quotation(quotation);

    ExecutionResult::ActivationChanged
}

/// ? p q -- calls if true, otherwise call
pub fn conditional_branch(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let false_branch = ctx.receiver;
    let [condition, true_branch] = inputs(ctx);
    let branch = if condition == bool_object(ctx, false) {
        false_branch
    } else {
        true_branch
    };

    // SAFETY: safe
    let branch = unsafe { branch.cast::<Quotation>() };

    ctx.interpreter.add_quotation(branch);
    ExecutionResult::ActivationChanged
}

pub fn parent(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let p = ctx.vm.specials().quotation_traits;
    ctx.outputs[0] = p.into();
    ExecutionResult::Normal
}
