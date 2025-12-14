// TODO: remove this unused
#![allow(unused)]

use crate::{
    Array, ByteArray, BytecodeCompiler, ExecutionResult, Handle, Message,
    ObjectType, ParsedToken, Parser, PrimitiveContext, Tagged, Value,
};

// TODO: this function should become fully stateless
pub fn parse_next(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let heap = &mut ctx.heap;
    let state = &mut ctx.state;

    // SAFETY: must be parser, can't be called otherwise
    let mut parser = unsafe { ctx.receiver.cast::<Parser>() };

    let Some(token) = parser.parse_next() else {
        ctx.state
            .push(ctx.vm.shared.specials.false_object.as_value());
        return ExecutionResult::Normal;
    };

    match token {
        ParsedToken::Float(_float) => {
            unimplemented!("Floats not implemented yet");
        }
        ParsedToken::Fixnum(num) => {
            state.push(Value::from_fixnum(num));
        }
        ParsedToken::String(token) => {
            let s = parser.get_token_string(token);
            let ba = ctx.vm.intern_string(s, heap);
            state.push(ba.as_value());
        }
        ParsedToken::Identifier(token) => {
            let s = parser.get_token_string(token);
            let ba = ctx.vm.intern_string(s, heap);
            let message = ctx.vm.intern_message(ba, heap);
            state.push(message.as_value());
        }
    }

    ExecutionResult::Normal
}

// TODO: this is not correct, use parse_complete as correct example
pub fn parse_quotation(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let end = ctx.vm.intern_string_message("]", ctx.heap);
    ctx.state.push(end.as_value());
    let res = parse_until(ctx);

    if res != ExecutionResult::Normal {
        unimplemented!("TODO: error handling");
    }

    // SAFETY: must exist
    let accumulator_value = unsafe { ctx.state.pop_unchecked() };
    // SAFETY: this is safe
    let accumulator =
        unsafe { accumulator_value.as_handle_unchecked().cast::<Array>() };
    let code_block = BytecodeCompiler::compile(&ctx.vm.shared, accumulator);
    let code = ctx.vm.shared.code_heap.push(code_block);

    // TODO: implement correct sizes here
    let quot = ctx.heap.allocate_quotation(accumulator, code, 0, 0);
    ctx.state.push(quot.into());
    ExecutionResult::Normal
}

// -- array
pub fn parse_complete(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let mut accumulator = Vec::new();

    let res = parse_until_inner(ctx, None, &mut accumulator);
    if res != ExecutionResult::Normal {
        return ExecutionResult::Panic("Parsing failed!");
    }

    let accumulated = ctx.heap.allocate_array(&accumulator);
    // SAFETY: just created, will become handle there anyways
    ctx.outputs[0] = unsafe { accumulated.promote_to_handle().into() };

    ExecutionResult::Normal
}

// TODO: this is not correct, use parse_complete as correct example
// end -- array | called on parser
pub fn parse_until(ctx: &mut PrimitiveContext) -> ExecutionResult {
    if ctx.state.depth() < 1 {
        return ExecutionResult::Panic("Datastack underflow");
    }

    let mut accumulator = Vec::new();
    // SAFETY: depth check
    let end = unsafe { ctx.state.pop_unchecked() };
    // SAFETY: heap deletion will be paused while parsing and requires Message
    let end = unsafe { end.as_handle_unchecked().cast::<Message>() };

    let res = parse_until_inner(ctx, Some(end), &mut accumulator);
    if res != ExecutionResult::Normal {
        return ExecutionResult::Panic("Parsing failed!");
    }

    let accumulated = ctx.heap.allocate_array(&accumulator);
    ctx.state.push(accumulated.into());

    ExecutionResult::Normal
}

// parser --
fn parse_until_inner(
    ctx: &mut PrimitiveContext,
    end: Option<Handle<Message>>,
    accum: &mut Vec<Value>,
) -> ExecutionResult {
    // SAFETY: must be parser, can't be called otherwise
    let parser = unsafe { ctx.receiver.cast::<Parser>() };

    loop {
        let res = parse_next(ctx);
        if res != ExecutionResult::Normal {
            break;
        }
        let state = &mut ctx.state;
        let vm = &ctx.vm;

        // SAFETY: parse_next must return
        let next = unsafe { state.pop_unchecked() };

        if next == vm.shared.specials.false_object.as_value() {
            break;
        }

        if !next.is_object() {
            accum.push(next);
            continue;
        }

        // SAFETY: heap deletion will be paused while parsing;
        let handle = unsafe { next.as_heap_handle_unchecked() };

        // SAFETY: checked
        if unsafe { handle.header.object_type().unwrap_unchecked() }
            != ObjectType::Message
        {
            accum.push(next);
            continue;
        }

        // SAFETY: checked
        let message = unsafe { handle.cast::<Message>() };

        if Some(message) == end {
            break;
        }

        // SAFETY: when parsing we can be sure this is valid utf8
        let name = unsafe { message.value.as_ref().as_utf8().expect("utf8") };

        // if let Some(_parser) = ctx.parsers.get(name) {
        //     unimplemented!("parses not implemented yet");
        // }

        accum.push(next);
    }

    ExecutionResult::Normal
}
