// TODO: remove this unused
#![allow(unused)]

use crate::{
    Array, ByteArray, BytecodeCompiler, ExecutionResult, Handle, Message,
    ObjectType, ParsedToken, Parser, PrimitiveContext, Quotation, Tagged,
    Value, get_primitive, primitive_index,
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
    let mut accumulator = Vec::new();

    let end = ctx.vm.intern_string_message("]", ctx.heap);

    let res = parse_until_inner(ctx, Some(end), &mut accumulator);
    if res != ExecutionResult::Normal {
        return ExecutionResult::Panic("Parsing failed!");
    }

    // SAFETY: TODO: must be added to handleset
    let body =
        unsafe { ctx.heap.allocate_array(&accumulator).promote_to_handle() };
    let block = BytecodeCompiler::compile(&ctx.vm.shared, body);
    let code = ctx.vm.shared.code_heap.push(block);
    // TODO: this must be updated
    let quotation = ctx.heap.allocate_quotation(body, code, 0, 0);
    // SAFETY: just allocated
    let quotation = unsafe { quotation.promote_to_handle() };
    // SAFETY: just created, will become handle there anyways
    ctx.outputs[0] = quotation.as_value_handle();

    ExecutionResult::Normal
}

pub fn parse_object(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let mut accumulator = Vec::new();

    let end = ctx.vm.intern_string_message("|)", ctx.heap);

    let res = parse_until_inner(ctx, Some(end), &mut accumulator);
    if res != ExecutionResult::Normal {
        return ExecutionResult::Panic("Parsing failed!");
    }

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
// end -- array
pub fn parse_until(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let mut accumulator = Vec::new();

    // SAFETY: must exist
    let end = unsafe { ctx.state.pop_unchecked() };
    // SAFETY: TODO: maybe check in future but input expects this
    let end = unsafe { end.as_handle_unchecked().cast::<Message>() };

    let res = parse_until_inner(ctx, Some(end), &mut accumulator);
    if res != ExecutionResult::Normal {
        return ExecutionResult::Panic("Parsing failed!");
    }

    let accumulated = ctx.heap.allocate_array(&accumulator);
    // SAFETY: just created, will become handle there anyways
    ctx.outputs[0] = unsafe { accumulated.promote_to_handle().into() };

    ExecutionResult::Normal
}

// parser --
fn parse_until_inner<'m, 'ex, 'arg>(
    ctx: &'m mut PrimitiveContext<'ex, 'arg>,
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

        // SAFETY: parse_next must return
        let next = unsafe { ctx.state.pop_unchecked() };

        if next == ctx.vm.shared.specials.false_object.as_value() {
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

        // TODO: this should invoke a new call
        if name == "[" {
            let message = get_primitive(primitive_index("["));
            let mut inputs = &[];
            let mut outputs = [Handle::zero(); 1];
            let mut ctx2 = ctx.new_invoke(parser.into(), inputs, &mut outputs);
            // let res = message.call_with_context(&mut ctx2);
            let res = parse_quotation(&mut ctx2);
            // println!("outputs: {:?}", outputs[0]);
            accum.push(outputs[0].into());
            continue;
        }
        // if let Some(_parser) = ctx.parsers.get(name) {
        //     unimplemented!("parses not implemented yet");
        // }

        accum.push(next);
    }

    ExecutionResult::Normal
}
