use crate::{
    Allocator, Array, BytecodeCompiler, ExecutionResult, PrimitiveContext,
};

pub fn array_to_quotation(ctx: &mut PrimitiveContext) -> ExecutionResult {
    // SAFETY: required by contract, will be eruntime checked
    let array = unsafe { ctx.receiver.cast::<Array>() };
    let code = BytecodeCompiler::compile(&ctx.vm.shared, ctx.heap, array);
    let map = ctx.heap.allocate_executable_map(code, 0, 0);

    // SAFETY: setup by runtime
    let activation = unsafe { ctx.interpreter.context_unchecked().activation };
    let quotation = ctx.heap.allocate_quotation(map, activation);

    ctx.outputs[0] = quotation.into();
    ExecutionResult::Normal
}

pub fn parent(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let p = ctx.vm.specials().array_traits;
    ctx.outputs[0] = p.into();
    ExecutionResult::Normal
}

pub fn size(ctx: &mut PrimitiveContext) -> ExecutionResult {
    // SAFETY: this is safe
    let arr = unsafe { ctx.receiver.cast::<Array>() };
    ctx.outputs[0] = arr.size.into();
    ExecutionResult::Normal
}

// ( size fill -- new ) | rec: array (or factory)
pub fn array_new(ctx: &mut PrimitiveContext) -> ExecutionResult {
    // Expect two inputs: size and the fill value
    let [size_val, fill_val] = crate::primitives::inputs(ctx);

    if !size_val.is_fixnum() {
        return ExecutionResult::Panic("arrayNew: size must be a fixnum");
    }

    // SAFETY: safe by contract
    let size = unsafe { size_val.as_fixnum::<usize>() };

    // Get the raw value to fill with (unwrapping the handle/object)
    let raw_fill = fill_val.inner();

    // SAFETY: we initialize
    let mut arr = unsafe { ctx.heap.allocate_raw_array(size) };

    // Fill the mutable slice of the new array with the user-provided value
    arr.fields_mut().fill(raw_fill);

    // SAFETY: object is now fully initialized
    ctx.outputs[0] = arr.into();
    ExecutionResult::Normal
}

// ( index -- value ) | rec: array
pub fn array_at(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let [index_val] = crate::primitives::inputs(ctx);
    // SAFETY: safe
    let arr = unsafe { ctx.receiver.cast::<Array>() };

    if !index_val.is_fixnum() {
        return ExecutionResult::Panic("arrayAt: index must be a fixnum");
    }

    // SAFETY: safe if contract holds
    let index = unsafe { index_val.as_fixnum::<usize>() };

    if index >= arr.inner().size() {
        return ExecutionResult::Panic("arrayAt: index out of bounds");
    }

    // SAFETY: Bounds checked above
    let val = unsafe { arr.inner().get_unchecked(index) };

    // SAFETY: Values stored in array are valid
    unsafe {
        ctx.outputs[0] = val.as_handle_unchecked();
    }
    ExecutionResult::Normal
}

// ( value index -- ) | rec: array
pub fn array_at_put(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let [value, index_val] = crate::primitives::inputs(ctx);
    // SAFETY: safe if contract holds
    let mut arr = unsafe { ctx.receiver.cast::<Array>() };

    // SAFETY: safe if contract holds
    let index = unsafe { index_val.as_fixnum::<usize>() };

    // SAFETY: Bounds checked above
    unsafe {
        arr.set_unchecked(index, value.inner());
    }

    ExecutionResult::Normal
}
