use crate::{
    ByteArray, ExecutionResult, HeapValue, ObjectType, ParsedToken, PrimitiveParserContext, Tagged,
    Value,
};

pub fn parse_next(ctx: &mut PrimitiveParserContext) -> ExecutionResult {
    let p = &mut ctx.parser;
    let heap = &mut ctx.heap;
    let state = &mut ctx.state;

    let Some(token) = p.parse_next() else {
        ctx.state
            .push(ctx.thread.vm.shared.specials.false_object.inner());
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
            // TODO: use string interning
            // for that we can use a new type
            // like Word { ba: ByteArray }
            // this way we can also differentiate between Strings and Messages
            let ba = heap.allocate_bytearray_data(s.as_bytes());
            let value = ba.as_value();
            state.push(value);
        }
    }

    ExecutionResult::Normal
}

pub fn parse_until_inner(ctx: &mut PrimitiveParserContext) -> ExecutionResult {
    let state = &mut ctx.state;
    if state.depth() < 2 {
        return ExecutionResult::Panic("Datastack underflow");
    }
    let end = unsafe { state.pop_unchecked() };
    let accum = unsafe { state.pop_unchecked() };

    while parse_next(ctx) != ExecutionResult::Normal {
        let state = &mut ctx.state;
        let vm = &ctx.thread.vm;

        // Safety: parse_next must return
        let next = unsafe { state.pop_unchecked() };
        if next == vm.shared.specials.false_object.inner() {
            return ExecutionResult::Panic(
                "Illegal: End of Input reached while trying to parse until",
            );
        }

        if !next.is_object() {
            state.push(next);
            continue;
        }

        // Safety: heap deletion will be paused while parsing;
        let handle = unsafe { next.as_heap_handle_unchecked() };

        // Safety: checked
        if unsafe { handle.header.object_type().unwrap_unchecked() } != ObjectType::ByteArray {
            state.push(next);
            continue;
        }

        let ba = unsafe { handle.cast::<ByteArray>() };

        let bytes = ba.as_bytes();
    }

    ExecutionResult::Normal
}
