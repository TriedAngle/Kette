use crate::{
    Allocator, Array, BytecodeCompiler, ExecutionResult, PrimitiveContext,
};

pub fn array_to_quotation(ctx: &mut PrimitiveContext) -> ExecutionResult {
    // SAFETY: required by contract, will be eruntime checked
    let array = unsafe { ctx.receiver.cast::<Array>() };
    let code = BytecodeCompiler::compile(&ctx.vm.shared, ctx.heap, array);
    let map = ctx.heap.allocate_executable_map(code, 0, 0);

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

// ( size -- new ) | rec: array
pub fn array_new(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let [size_val] = crate::primitives::inputs(ctx);

    if !size_val.is_fixnum() {
        return ExecutionResult::Panic("arrayNew: size must be a fixnum");
    }

    // SAFETY: safe by contract
    let size = unsafe { size_val.as_fixnum::<usize>() };

    let default_val = ctx.vm.specials().false_object.as_value();

    // SAFETY: we initialize
    let mut arr = unsafe { ctx.heap.allocate_raw_array(size) };

    arr.fields_mut().fill(default_val);

    // SAFETY: object is now fully initialized
    ctx.outputs[0] = arr.into();
    ExecutionResult::Normal
}

// ( index -- value ) | rec: array
pub fn array_at(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let [index_val] = crate::primitives::inputs(ctx);
    // SAFETY: safe if contract holds
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

    if !index_val.is_fixnum() {
        return ExecutionResult::Panic("arrayAtPut: index must be a fixnum");
    }

    // SAFETY: safe if contract holds
    let index = unsafe { index_val.as_fixnum::<usize>() };

    if index >= arr.inner().size() {
        return ExecutionResult::Panic("arrayAtPut: index out of bounds");
    }

    // SAFETY: Bounds checked above
    unsafe {
        arr.set_unchecked(index, value.inner());
    }

    ExecutionResult::Normal
}
