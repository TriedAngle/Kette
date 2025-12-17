// TODO: remove this unused
#![allow(unused)]

use std::ops::Deref;

use crate::{
    Array, ByteArray, BytecodeCompiler, ExecutionResult, Handle, LookupResult,
    Message, Method, Object, ObjectType, ParsedToken, Parser, PrimitiveContext,
    PrimitiveMessageIndex, Quotation, Selector, SlotTags, Tagged, Value,
    Vector, get_primitive, primitive_index,
};

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
        ParsedToken::Float(float) => {
            let float = heap.allocate_float(float);
            state.push(float.into());
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
    // SAFETY: must exist by contract
    let mut accumulator = unsafe { ctx.inputs[0].cast::<Vector>() };

    let vector = Vector::new(ctx.heap, &ctx.vm.shared, 100);
    // SAFETY: just created
    let mut body_accum = unsafe { vector.promote_to_handle() };

    let end = ctx.vm.intern_string_message("]", ctx.heap);

    let res = parse_until_inner(ctx, Some(end), body_accum);
    if res != ExecutionResult::Normal {
        return ExecutionResult::Panic("Parsing failed!");
    }

    // SAFETY: TODO: must be added to handleset
    let body = unsafe {
        ctx.heap
            .allocate_array(body_accum.as_slice())
            .promote_to_handle()
    };
    let block = BytecodeCompiler::compile(&ctx.vm.shared, body);
    let code = ctx.vm.shared.code_heap.push(block);
    // TODO: this must be updated
    let quotation = ctx.heap.allocate_quotation(body, code, 0, 0);
    accumulator.push(quotation.into(), ctx.heap, &ctx.vm.shared);

    ctx.outputs[0] = accumulator.into();

    ExecutionResult::Normal
}

pub fn parse_object(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let vector = Vector::new(ctx.heap, &ctx.vm.shared, 0);
    // SAFETY: just created
    let mut accumulator = unsafe { vector.promote_to_handle() };

    let end = ctx.vm.intern_string_message("|)", ctx.heap);

    let res = parse_until_inner(ctx, Some(end), accumulator);
    if res != ExecutionResult::Normal {
        return ExecutionResult::Panic("Parsing failed!");
    }

    // TODO: implement this

    ExecutionResult::Normal
}

fn parse_effect_inner(
    ctx: &mut PrimitiveContext,
) -> Result<(Handle<Vector>, Handle<Vector>), &'static str> {
    // SAFETY: must be parser, can't be called otherwise
    let mut parser = unsafe { ctx.receiver.cast::<Parser>() };

    // Expect "("
    let open = parser.parse_next().ok_or("Parsing Effect: Missing '('")?;
    match open {
        ParsedToken::Identifier(t) if parser.get_token_string(t) == "(" => {}
        _ => return Err("Parsing Effect: Expected '('"),
    }

    let in_vec = Vector::new(ctx.heap, &ctx.vm.shared, 0);
    // SAFETY: just created
    let mut inputs = unsafe { in_vec.promote_to_handle() };

    let out_vec = Vector::new(ctx.heap, &ctx.vm.shared, 0);
    // SAFETY: just created
    let mut outputs = unsafe { out_vec.promote_to_handle() };

    let mut reading_inputs = true;
    let mut saw_separator = false;

    loop {
        let tok = parser
            .parse_next()
            .ok_or("Parsing Effect: Unterminated effect (missing ')')")?;

        match tok {
            ParsedToken::Identifier(t) => {
                let s = parser.get_token_string(t);

                if s == "--" {
                    if !reading_inputs {
                        return Err("Parsing Effect: Duplicate '--'");
                    }
                    reading_inputs = false;
                    saw_separator = true;
                    continue;
                }

                if s == ")" {
                    if !saw_separator {
                        return Err("Parsing Effect: Missing '--'");
                    }
                    break;
                }

                // Treat every other identifier as a stack-name; store as Message.
                let msg = ctx.vm.intern_string_message(s, ctx.heap);
                if reading_inputs {
                    inputs.push(msg.as_value(), ctx.heap, &ctx.vm.shared);
                } else {
                    outputs.push(msg.as_value(), ctx.heap, &ctx.vm.shared);
                }
            }

            ParsedToken::String(_) => {
                return Err(
                    "Parsing Effect: Strings are not allowed inside effect",
                );
            }
            ParsedToken::Fixnum(_) => {
                return Err(
                    "Parsing Effect: Numbers are not allowed inside effect",
                );
            }
            ParsedToken::Float(_) => {
                return Err(
                    "Parsing Effect: Floats are not allowed inside effect",
                );
            }
        }
    }

    Ok((inputs, outputs))
}

/// should parse: `: <name> <effect> <body> ;`
/// ( `:` is ignored, its already "parsed" when this function is called)
pub fn parse_method(ctx: &mut PrimitiveContext) -> ExecutionResult {
    // SAFETY: must be parser, can't be called otherwise
    let mut parser = unsafe { ctx.receiver.cast::<Parser>() };
    // SAFETY: must exist by contract
    let mut accumulator = unsafe { ctx.inputs[0].cast::<Vector>() };

    // Parse name
    let name_tok = match parser.parse_next() {
        Some(t) => t,
        None => return ExecutionResult::Panic("Parsing Method: Missing Name"),
    };

    let name_str = match name_tok {
        ParsedToken::Identifier(t) => parser.get_token_string(t),
        _ => {
            return ExecutionResult::Panic(
                "Parsing Method: Name must be an identifier",
            );
        }
    };

    let name = ctx.vm.intern_string(name_str, ctx.heap);

    // Parse effect
    let (inputs_vec, outputs_vec) = match parse_effect_inner(ctx) {
        Ok(v) => v,
        Err(e) => return ExecutionResult::Panic(e),
    };

    // Convert Vectors to Arrays for Method storage
    // SAFETY: allocating this here
    let inputs_arr = unsafe {
        ctx.heap
            .allocate_array(inputs_vec.as_slice())
            .promote_to_handle()
    };
    // SAFETY: allocating this here
    let outputs_arr = unsafe {
        ctx.heap
            .allocate_array(outputs_vec.as_slice())
            .promote_to_handle()
    };

    // Parse body until ';'
    let body_vec = Vector::new(ctx.heap, &ctx.vm.shared, 100);
    // SAFETY: just created
    let mut body_accum = unsafe { body_vec.promote_to_handle() };

    let end = ctx.vm.intern_string_message(";", ctx.heap);

    let res = parse_until_inner(ctx, Some(end), body_accum);
    if res != ExecutionResult::Normal {
        return ExecutionResult::Panic("Parsing Method: Parsing body failed!");
    }

    // Compile into a quotation (with effect counts)
    // SAFETY: allocating here
    let body_arr = unsafe {
        ctx.heap
            .allocate_array(body_accum.as_slice())
            .promote_to_handle()
    };
    let block = BytecodeCompiler::compile(&ctx.vm.shared, body_arr);
    let code = ctx.vm.shared.code_heap.push(block);

    let effect = ctx
        .heap
        .allocate_effect_object(inputs_arr.into(), outputs_arr.into());
    let method_map =
        ctx.heap.allocate_method_map(name.into(), code, &[], effect);
    let method = ctx.heap.allocate_method_object(method_map);

    accumulator.push(method.into(), ctx.heap, &ctx.vm.shared);

    ctx.outputs[0] = accumulator.into();

    ExecutionResult::Normal
}

// -- array
pub fn parse_complete(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let vector = Vector::new(ctx.heap, &ctx.vm.shared, 100);
    // SAFETY: just created
    let mut accumulator = unsafe { vector.promote_to_handle() };

    let res = parse_until_inner(ctx, None, accumulator);
    if res != ExecutionResult::Normal {
        return ExecutionResult::Panic("Parsing failed!");
    }

    let accumulated = ctx.heap.allocate_array(accumulator.as_slice());
    // SAFETY: just created, will become handle there anyways
    let acummulated = unsafe { accumulated.promote_to_handle() };

    ctx.outputs[0] = acummulated.as_value_handle();

    ExecutionResult::Normal
}

// TODO: this is not correct, use parse_complete as correct example
// end -- array
pub fn parse_until(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let vector = Vector::new(ctx.heap, &ctx.vm.shared, 10);
    // SAFETY: just created
    let mut accumulator = unsafe { vector.promote_to_handle() };

    // SAFETY: must exist
    let end = unsafe { ctx.state.pop_unchecked() };
    // SAFETY: TODO: maybe check in future but input expects this
    let end = unsafe { end.as_handle_unchecked().cast::<Message>() };

    let res = parse_until_inner(ctx, Some(end), accumulator);
    if res != ExecutionResult::Normal {
        return ExecutionResult::Panic("Parsing failed!");
    }

    // trimming
    let accumulated = ctx.heap.allocate_array(accumulator.as_slice());
    // SAFETY: just created, will become handle there anyways
    ctx.outputs[0] = unsafe { accumulated.promote_to_handle().into() };

    ExecutionResult::Normal
}

// parser --
fn parse_until_inner<'m, 'ex, 'arg>(
    ctx: &'m mut PrimitiveContext<'ex, 'arg>,
    end: Option<Handle<Message>>,
    mut accum: Handle<Vector>,
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
            accum.push(next, ctx.heap, &ctx.vm.shared);
            continue;
        }

        // SAFETY: heap deletion will be paused while parsing;
        let handle = unsafe { next.as_heap_handle_unchecked() };

        // SAFETY: checked
        if unsafe { handle.header.object_type().unwrap_unchecked() }
            != ObjectType::Message
        {
            accum.push(next, ctx.heap, &ctx.vm.shared);
            continue;
        }

        // SAFETY: checked
        let message = unsafe { handle.cast::<Message>() };

        if Some(message) == end {
            break;
        }

        let parsers = ctx.vm.specials().parsers;
        // SAFETY: must be valid
        let name = unsafe { message.value.promote_to_handle() };
        let selector = Selector::new(name, ctx.vm.shared.clone());
        let lookup = selector.lookup_object(&parsers.as_value());
        match lookup {
            LookupResult::Found {
                object,
                slot,
                slot_index,
            } => {
                let tags = slot.tags();
                if tags.contains(SlotTags::EXECUTABLE) {
                    let res = if tags.contains(SlotTags::PRIMITIVE) {
                        let id = slot
                            .value
                            .as_tagged_fixnum::<usize>()
                            .expect("primitive must have fixnum");
                        // SAFETY: must store valid primitive idx if primitive executable
                        let message_idx = unsafe {
                            PrimitiveMessageIndex::from_usize(id.into())
                        };
                        ctx.state.push(accum.as_value());
                        ctx.interpreter
                            .primitive_send(ctx.receiver, message_idx)
                    } else {
                        // SAFETY: must be
                        let method = unsafe {
                            slot.value
                                .as_heap_handle_unchecked()
                                .cast::<Method>()
                        };
                        ctx.state.push(accum.as_value());
                        ctx.interpreter.add_method(ctx.receiver, method);
                        ctx.interpreter.execute_with_depth()
                    };

                    // SAFETY: safe if adhere to protocol
                    // all parsers do: self = parser ( accum -- accum )
                    accum = unsafe {
                        ctx.state
                            .pop()
                            .expect("must exist")
                            .as_handle_unchecked()
                            .cast()
                    };
                } else {
                    accum.push(slot.value, ctx.heap, &ctx.vm.shared);
                }
            }
            LookupResult::None => accum.push(next, ctx.heap, &ctx.vm.shared),
        }
    }

    ExecutionResult::Normal
}

// TODO: these should be moved into unserspace
pub fn parse_line_comment(ctx: &mut PrimitiveContext) -> ExecutionResult {
    // SAFETY: must be parser, can't be called otherwise
    let mut parser = unsafe { ctx.receiver.cast::<Parser>() };
    // SAFETY: must exist by contract
    let mut accumulator = unsafe { ctx.inputs[0].cast::<Vector>() };

    // Try to read until the next newline
    if parser.read_until("\n").is_none() {
        // If no newline is found, the comment extends to the end of the file.
        // read_until returns None without advancing offset if not found,
        // so we manually consume the rest of the code.
        parser.offset = parser.end;
    }

    ctx.outputs[0] = accumulator.into();

    ExecutionResult::Normal
}

pub fn parse_block_comment(ctx: &mut PrimitiveContext) -> ExecutionResult {
    // SAFETY: must be parser, can't be called otherwise
    let mut parser = unsafe { ctx.receiver.cast::<Parser>() };
    // SAFETY: must exist by contract
    let accumulator = unsafe { ctx.inputs[0].cast::<Vector>() };

    let mut depth: usize = 1;

    while parser.offset + 1 < parser.end {
        let a = parser.code[parser.offset];
        let b = parser.code[parser.offset + 1];

        // Nested open
        if a == b'/' && b == b'*' {
            depth += 1;
            parser.offset += 2;
            continue;
        }

        // Close
        if a == b'*' && b == b'/' {
            depth -= 1;
            parser.offset += 2;

            if depth == 0 {
                ctx.outputs[0] = accumulator.into();
                return ExecutionResult::Normal;
            }

            continue;
        }

        parser.offset += 1;
    }

    ExecutionResult::Panic(
        "Parsing Error: Unterminated block comment (missing '*/')",
    )
}
