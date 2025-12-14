use crate::{
    ActivationType, ExecutionResult, PrimitiveContext, Quotation,
    primitives::{bool_object, inputs, outputs},
};

// TODO: implement this
pub fn call(ctx: &mut PrimitiveContext) -> ExecutionResult {
    // SAFETY: this is safe
    let quotation = unsafe { ctx.receiver.cast::<Quotation>() };
    let activation_object =
        ctx.heap.allocate_quotation_activation(quotation, &[]);
    ctx.interpreter
        .activations
        .new_activation(activation_object, ActivationType::Quotation);
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
    let quot = ctx.vm.shared.specials.dip_quotation;

    let activation_object = ctx.heap.allocate_quotation_activation(quot, &[]);
    ctx.interpreter
        .activations
        .new_activation(activation_object, ActivationType::Quotation);
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
    let activation_object = ctx.heap.allocate_quotation_activation(branch, &[]);
    ctx.interpreter
        .activations
        .new_activation(activation_object, ActivationType::Quotation);
    ExecutionResult::ActivationChanged
}
