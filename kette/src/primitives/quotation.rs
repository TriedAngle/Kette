use crate::{
    ExecutionResult, PrimitiveContext,
    primitives::{bool_object, inputs, outputs},
};

// TODO: implement this
pub fn call(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let _ = ctx;
    ExecutionResult::Normal
}

// TODO: implement this
/// removes x, calls q, puts x again
/// x q -- x
pub fn dip(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let [x] = inputs(ctx);

    let quote = ctx.receiver;

    // TODO: do executable map check and execute.
    // TODO: add callstack once added
    ctx.state.push_return(x.into());
    tracing::error!("TRYING TO CALL {quote:?}, BUT CALL NOT IMPLEMENTED");
    outputs(ctx, [x]);
    ExecutionResult::Normal
}

// TODO: implement this
/// ? p q -- calls if true, otherwise call
pub fn conditional_branch(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let false_branch = ctx.receiver;
    let [condition, true_branch] = inputs(ctx);
    if condition == bool_object(ctx, false) {
        let _ = false_branch;
    } else {
        let _ = true_branch;
    }
    ExecutionResult::Normal
}
