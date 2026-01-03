use crate::{
    ActivationType, Allocator, ExecutionResult, Handle, PrimitiveContext, Quotation, primitives::{bool_object, inputs, outputs}
};

pub fn call(ctx: &mut PrimitiveContext) -> ExecutionResult {
    // SAFETY: this is safe
    let quotation = unsafe { ctx.receiver.cast::<Quotation>() };

    let receiver = ctx
        .interpreter
        .current_activation()
        .map(|a| a.object.receiver)
        .unwrap_or(ctx.vm.specials().false_object.as_value_handle());

    let activation_object =
        ctx.heap
            .allocate_quotation_activation(receiver, quotation, &[]);
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


    let map = ctx.vm.shared.specials.dip_map;
    let quot = ctx.heap.allocate_quotation(map, unsafe { Handle::null() });

    let receiver = ctx
        .interpreter
        .current_activation()
        .map(|a| a.object.receiver)
        .unwrap_or(ctx.vm.specials().false_object.as_value_handle());

    let activation_object =
        ctx.heap.allocate_quotation_activation(receiver, quot, &[]);

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
    let receiver = ctx
        .interpreter
        .current_activation()
        .map(|a| a.object.receiver)
        .unwrap_or(ctx.vm.specials().false_object.as_value_handle());

    // SAFETY: safe
    let branch = unsafe { branch.cast::<Quotation>() };
    let activation_object =
        ctx.heap
            .allocate_quotation_activation(receiver, branch, &[]);
    ctx.interpreter
        .activations
        .new_activation(activation_object, ActivationType::Quotation);
    ExecutionResult::ActivationChanged
}

pub fn parent(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let p = ctx.vm.specials().quotation_traits;
    ctx.outputs[0] = p.into();
    ExecutionResult::Normal
}
