use crate::{
    Array, BytecodeCompiler, ExecutionResult, PrimitiveContext, Tagged,
};

pub fn array_to_quotation(ctx: &mut PrimitiveContext) -> ExecutionResult {
    // SAFETY: required by contract, will be eruntime checked
    let array = unsafe { ctx.receiver.cast::<Array>() };
    let compiled = BytecodeCompiler::compile(&ctx.vm.shared, array);
    let block = ctx.vm.shared.code_heap.push(compiled);
    let quotation =
        ctx.heap
            .allocate_quotation(array, block, Tagged::new_value(0));

    // SAFETY: no gc here
    ctx.outputs[0] = unsafe { quotation.promote_to_handle().into() };
    ExecutionResult::Normal
}
