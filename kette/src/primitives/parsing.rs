// TODO: remove this unused
#![allow(unused)]

use crate::{
    ByteArray, ExecutionResult, ObjectType, ParsedToken,
    PrimitiveParserContext, Value,
};

pub fn parse_next(ctx: &mut PrimitiveParserContext) -> ExecutionResult {
    let p = &mut ctx.parser;
    let heap = &mut ctx.heap;
    let state = &mut ctx.state;

    let Some(token) = p.parse_next() else {
        ctx.state
            .push(ctx.vm.shared.specials.false_object.as_value());
        return ExecutionResult::Normal;
    };

    match token {
        ParsedToken::Float(_float) => {
            unimplemented!("Floats not implemented yet");
        }
        ParsedToken::Fixnum(num) => {
            ctx.state.push(Value::from_fixnum(num));
        }
        ParsedToken::Identifier(token) => {
            let s = p.get_token_string(token);
            let ba = ctx.vm.intern_string(s, heap);
            let value = ba.as_value();
            state.push(value);
        }
    }

    ExecutionResult::Normal
}

pub fn parse_until(ctx: &mut PrimitiveParserContext) -> ExecutionResult {
    if ctx.state.depth() < 1 {
        return ExecutionResult::Panic("Datastack underflow");
    }

    let mut accum = Vec::new();
    // SAFETY: depth check
    let end = unsafe { ctx.state.pop_unchecked() };
    // SAFETY: heap deletion will be paused while parsing and requires ByteArray
    let end = unsafe { end.as_handle_unchecked().cast::<ByteArray>() };
    // SAFETY: source must be utf8 encoded
    let end = unsafe { str::from_utf8_unchecked(end.as_bytes()) };

    let res = parse_until_inner(ctx, end, &mut accum);
    if res != ExecutionResult::Normal {
        return ExecutionResult::Panic("Parsing failed!");
    }

    unimplemented!()
    // let array =
}

fn parse_until_inner(
    ctx: &mut PrimitiveParserContext,
    _end: &str,
    _accum: &mut [Value],
) -> ExecutionResult {
    let state = &mut ctx.state;
    if state.depth() < 2 {
        return ExecutionResult::Panic("Datastack underflow");
    }

    while parse_next(ctx) != ExecutionResult::Normal {
        let state = &mut ctx.state;
        let vm = &ctx.vm;

        // SAFETY: parse_next must return
        let next = unsafe { state.pop_unchecked() };
        if next == vm.shared.specials.false_object.as_value() {
            return ExecutionResult::Panic(
                "Illegal: End of Input reached while trying to parse until",
            );
        }

        if !next.is_object() {
            state.push(next);
            continue;
        }

        // SAFETY: heap deletion will be paused while parsing;
        let handle = unsafe { next.as_heap_handle_unchecked() };

        // SAFETY: checked
        if unsafe { handle.header.object_type().unwrap_unchecked() }
            != ObjectType::ByteArray
        {
            state.push(next);
            continue;
        }

        // SAFETY: checked
        let ba = unsafe { handle.cast::<ByteArray>() };
        let bytes = ba.as_bytes();
        // SAFETY: when parsing we can be sure this is valid utf8
        let name = unsafe { str::from_utf8_unchecked(bytes) };

        if let Some(_parser) = ctx.parsers.get(name) {
            unimplemented!("parses not implemented yet");
        }

        state.push(next);
    }

    ExecutionResult::Normal
}
