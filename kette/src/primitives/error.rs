use crate::{
    ActivationObject, ExecutionResult, PrimitiveContext, Quotation, primitives::inputs
};

/// Primitive: `( tag handler body -- )`
/// Executes `body` (a quotation) with `handler` active for `tag`.
/// The handler is scoped ONLY to this body.
pub fn with_handler(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let [tag, handler] = inputs(ctx);

    let body = ctx.receiver;

    let heap_val = unsafe { body.as_heap_value_handle() };

    if !heap_val.is::<Quotation>() {
        return ExecutionResult::Panic("withHandler expects a quotation body");
    }

    // We also require handler to be a quotation, enforced by logic later or here
    let handler_heap = unsafe { handler.as_heap_value_handle() };
    if !handler_heap.is::<Quotation>() {
        return ExecutionResult::Panic("handler must be a quotation");
    }

    let quotation = unsafe { body.cast::<Quotation>() };

    // create a NEW activation and push it
    ctx.interpreter.add_quotation(quotation);

    // Attach the handler to that NEW activation
    let top_activation = ctx.interpreter.activations.current_mut()
        .expect("Activation must exist after add_quotation");
    
    top_activation.handlers.push((tag, handler));

    // 4. Run loop
    ExecutionResult::ActivationChanged
}

/// ( exception -- )
/// Signal an exception. Finds a handler and runs it *on top* of the current stack.
pub fn signal(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let [exception] = inputs(ctx);
    ctx.interpreter.signal_exception(exception)
}

/// Primitive: `( activation -- )`
/// Unwinds the stack so that `activation` becomes the top frame.
pub fn unwind(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let [activation_val] = inputs(ctx);

    let heap_val = unsafe { activation_val.as_heap_value_handle() };
    let Some(_activation) = heap_val.downcast_ref::<ActivationObject>() else {
        return ExecutionResult::Panic("unwind expects an Activation object");
    };

    let handle = unsafe { activation_val.cast::<ActivationObject>() };

    ctx.interpreter.unwind_to(handle)
}
