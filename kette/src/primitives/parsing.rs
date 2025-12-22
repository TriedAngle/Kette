// TODO: remove this unused
#![allow(unused)]

use std::ops::Deref;

use crate::{
    Allocator, Array, ByteArray, BytecodeCompiler, ExecutionResult, Handle,
    LookupResult, Message, Method, Object, ObjectType, ParsedToken, Parser,
    PrimitiveContext, PrimitiveMessageIndex, Quotation, Selector,
    SlotDescriptor, SlotTags, Tagged, Value, Vector, get_primitive,
    primitive_index,
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

    let body_accum = Vector::new(ctx.heap, &ctx.vm.shared, 100);

    let end = ctx.vm.intern_string_message("]", ctx.heap);

    let res = parse_until_inner(ctx, Some(end), body_accum);
    if res != ExecutionResult::Normal {
        return ExecutionResult::Panic("Parsing failed!");
    }

    // SAFETY: TODO: must be added to handleset
    let body = unsafe { ctx.heap.allocate_array(body_accum.as_slice()) };
    let block = BytecodeCompiler::compile(&ctx.vm.shared, body);
    let code = ctx.vm.shared.code_heap.push(block);
    // TODO: this must be updated
    let quotation = ctx.heap.allocate_quotation(body, code, 0, 0);
    accumulator.push(quotation.into(), ctx.heap, &ctx.vm.shared);

    ctx.outputs[0] = accumulator.into();

    ExecutionResult::Normal
}

pub fn parse_object(ctx: &mut PrimitiveContext) -> ExecutionResult {
    // SAFETY: must exist by contract (outer accumulator from parse_until_inner protocol)
    let mut outer_accum = unsafe { ctx.inputs[0].cast::<Vector>() };

    #[inline]
    fn message_name<'a>(v: Value) -> Option<&'a str> {
        if !v.is_object() {
            return None;
        }
        // SAFETY: checked is_object
        let h = unsafe { v.as_heap_handle_unchecked() };
        // SAFETY: object_type exists for objects
        let ty = unsafe { h.header.object_type().unwrap_unchecked() };
        if ty != ObjectType::Message {
            return None;
        }
        // SAFETY: ty checked
        let msg = unsafe { h.cast::<Message>() };
        // SAFETY: message.value is an interned ByteArray
        let ba = unsafe { msg.value.promote_to_handle() };
        // SAFETY: lifetime valid here
        Some(unsafe {
            std::mem::transmute::<&'_ str, &'a str>(
                ba.as_utf8().expect("must exist"),
            )
        })
    }

    #[inline]
    fn next_value(ctx: &mut PrimitiveContext) -> Value {
        let _ = parse_next(ctx);
        // SAFETY: parse_next always pushes something (token or false)
        unsafe { ctx.state.pop_unchecked() }
    }

    #[inline]
    fn as_method(v: Value) -> Option<Handle<Method>> {
        if !v.is_object() {
            return None;
        }
        // SAFETY: checked is_object
        let h = unsafe { v.as_heap_handle_unchecked() };
        // SAFETY: message.value is an interned ByteArray
        let ty = unsafe { h.header.object_type().unwrap_unchecked() };
        if ty != ObjectType::Method {
            return None;
        }
        // SAFETY: ty checked
        Some(unsafe { h.cast::<Method>() })
    }

    // NOTE: this assumes Method has a `map` field pointing to a map that has a `name: Tagged<ByteArray>`.
    // Adjust field names here if your structs differ.
    #[inline]
    fn method_name_tagged(method: Handle<Method>) -> Tagged<ByteArray> {
        // SAFETY: method/map must be valid by construction
        let map = unsafe { method.map.as_ref() };
        map.name
    }

    fn eval_expr(
        ctx: &mut PrimitiveContext,
        expr: &[Value],
    ) -> Result<Value, &'static str> {
        if expr.is_empty() {
            return Err("Parsing Object: Empty slot initializer");
        }
        let arr = ctx.heap.allocate_array(expr);
        let block = BytecodeCompiler::compile(&ctx.vm.shared, arr);
        let code = ctx.vm.shared.code_heap.push(block);
        let quot = ctx.heap.allocate_quotation(arr, code, 0, 0);

        let before = ctx.state.depth;
        ctx.interpreter.add_quotation(quot);
        let exec_res = ctx.interpreter.execute_with_depth();

        if exec_res != ExecutionResult::Normal {
            return Err("Parsing Object: Slot initializer execution failed");
        }

        let after = ctx.state.depth;
        if after != before + 1 {
            return Err(
                "Parsing Object: Slot initializer must leave exactly one value on stack",
            );
        }
        // SAFETY: after == before + 1 implies at least one value exists
        Ok(unsafe { ctx.state.pop_unchecked() })
    }

    enum InitEnd {
        Dot,
        ObjEnd,
    }

    // Parse initializer into `accum` until '.' OR '|)' ('.' optional at end).
    fn parse_until_dot_or_end<'m, 'ex, 'arg>(
        ctx: &'m mut PrimitiveContext<'ex, 'arg>,
        dot: Handle<Message>,
        obj_end: Handle<Message>,
        mut accum: Handle<Vector>,
    ) -> Result<(Handle<Vector>, InitEnd), &'static str> {
        loop {
            let res = parse_next(ctx);
            if res != ExecutionResult::Normal {
                return Err("Parsing Object: Parsing initializer failed");
            }
            // SAFETY: parse_next must return
            let next = unsafe { ctx.state.pop_unchecked() };
            if next == ctx.vm.shared.specials.false_object.as_value() {
                return Err(
                    "Parsing Object: Unterminated initializer (missing '.' or '|)')",
                );
            }

            if !next.is_object() {
                accum.push(next, ctx.heap, &ctx.vm.shared);
                continue;
            }

            // SAFETY: heap deletion paused while parsing
            let handle = unsafe { next.as_heap_handle_unchecked() };
            // SAFETY: object has object_type
            let ty = unsafe { handle.header.object_type().unwrap_unchecked() };

            if ty != ObjectType::Message {
                accum.push(next, ctx.heap, &ctx.vm.shared);
                continue;
            }

            // SAFETY: ty checked
            let message = unsafe { handle.cast::<Message>() };

            if message == dot {
                return Ok((accum, InitEnd::Dot));
            }
            if message == obj_end {
                return Ok((accum, InitEnd::ObjEnd));
            }

            // Allow parser-words inside initializer
            let parsers = ctx.vm.specials().parsers;
            // SAFETY: no gc
            let name = unsafe { message.value.promote_to_handle() };
            let selector = Selector::new(name, ctx.vm.shared.clone());
            let lookup = selector.lookup_object(&parsers.as_value());

            match lookup {
                LookupResult::Found { slot, .. } => {
                    let tags = slot.tags();
                    if tags.contains(SlotTags::EXECUTABLE) {
                        let res = if tags.contains(SlotTags::PRIMITIVE) {
                            let id = slot
                                .value
                                .as_tagged_fixnum::<usize>()
                                .expect("primitive must have fixnum");
                            // SAFETY: must store idx
                            let msg_idx = unsafe {
                                PrimitiveMessageIndex::from_usize(id.into())
                            };
                            ctx.state.push(accum.as_value());
                            ctx.interpreter
                                .primitive_send(ctx.receiver, msg_idx)
                        } else {
                            // SAFETY: must be method if not primitive
                            let method = unsafe {
                                slot.value
                                    .as_heap_handle_unchecked()
                                    .cast::<Method>()
                            };
                            ctx.state.push(accum.as_value());
                            ctx.interpreter.add_method(ctx.receiver, method);
                            ctx.interpreter.execute_with_depth()
                        };

                        if res != ExecutionResult::Normal {
                            return Err(
                                "Parsing Object: Parsing initializer failed",
                            );
                        }

                        // SAFETY: parser protocol (accum -- accum)
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
                LookupResult::None => {
                    accum.push(next, ctx.heap, &ctx.vm.shared)
                }
            }
        }
    }

    let dot = ctx.vm.intern_string_message(".", ctx.heap);
    let obj_end = ctx.vm.intern_string_message("|)", ctx.heap);

    let mut slot_descs: Vec<SlotDescriptor> = Vec::new();
    let mut assignable_inits: Vec<Value> = Vec::new();
    let mut assignable_offset: i64 = 0;

    loop {
        let v = next_value(ctx);
        if v == ctx.vm.shared.specials.false_object.as_value() {
            return ExecutionResult::Panic(
                "Parsing Object: Unterminated object (missing '|)')",
            );
        }

        let Some(head) = message_name(v) else {
            return ExecutionResult::Panic(
                "Parsing Object: Expected slot name, ':', or '|)'",
            );
        };

        if head == "|)" {
            break;
        }

        let mut tags = SlotTags::empty();

        // Don't strip the suffix, but note it for potential parent tagging
        let is_potential_parent = head.ends_with('*');

        // Read the next token to decide what kind of descriptor this is.
        let peek = next_value(ctx);
        if peek == ctx.vm.shared.specials.false_object.as_value() {
            return ExecutionResult::Panic(
                "Parsing Object: Unterminated object (missing '|)')",
            );
        }
        let Some(peek_str) = message_name(peek) else {
            return ExecutionResult::Panic(
                "Parsing Object: Expected '<-', '=', '.', or '|)' after slot name",
            );
        };

        // Intern slot name now (raw name including *)
        let name_ba = ctx.vm.intern_string(head, ctx.heap);
        let name_tagged: Tagged<ByteArray> = name_ba.into();

        // Shorthand: `<name> .` => assignable false
        if peek_str == "." {
            tags |= SlotTags::ASSIGNABLE;
            // Shorthands are always data slots, so check parent flag
            if is_potential_parent {
                tags |= SlotTags::PARENT;
            }
            let offset_value = Value::from_fixnum(assignable_offset);
            assignable_offset += 1;
            slot_descs.push(SlotDescriptor::new(
                name_tagged,
                tags,
                offset_value,
            ));
            assignable_inits
                .push(ctx.vm.shared.specials.false_object.as_value());
            continue;
        }

        // Shorthand: `<name>` as last before `|)` => assignable false
        if peek_str == "|)" {
            tags |= SlotTags::ASSIGNABLE;
            // Shorthands are always data slots, so check parent flag
            if is_potential_parent {
                tags |= SlotTags::PARENT;
            }
            let offset_value = Value::from_fixnum(assignable_offset);
            assignable_offset += 1;
            slot_descs.push(SlotDescriptor::new(
                name_tagged,
                tags,
                offset_value,
            ));
            assignable_inits
                .push(ctx.vm.shared.specials.false_object.as_value());
            break;
        }

        // Operator: "<-" or "="
        let is_assignable = match peek_str {
            ":=" => true,
            "=" => false,
            _ => {
                return ExecutionResult::Panic(
                    "Parsing Object: Expected '=', ':=', '.', or '|)' after slot name",
                );
            }
        };

        // Parse initializer until '.' OR '|)' (dot optional if ends at |))
        let expr_accum = Vector::new(ctx.heap, &ctx.vm.shared, 8);
        let (expr_accum, ended_by) =
            match parse_until_dot_or_end(ctx, dot, obj_end, expr_accum) {
                Ok(v) => v,
                Err(e) => return ExecutionResult::Panic(e),
            };

        let init_value = match eval_expr(ctx, expr_accum.as_slice()) {
            Ok(v) => v,
            Err(e) => return ExecutionResult::Panic(e),
        };

        // If initializer evaluates to a Method, mark slot EXECUTABLE.
        let is_method = as_method(init_value).is_some();
        if is_method {
            tags |= SlotTags::EXECUTABLE;
        }

        // Only mark as PARENT if it has the * suffix AND it is NOT a method.
        if !is_method && is_potential_parent {
            tags |= SlotTags::PARENT;
        }

        if is_assignable {
            tags |= SlotTags::ASSIGNABLE;
            let offset_value = Value::from_fixnum(assignable_offset);
            assignable_offset += 1;
            slot_descs.push(SlotDescriptor::new(
                name_tagged,
                tags,
                offset_value,
            ));
            assignable_inits.push(init_value);
            let setter_name = {
                // Keep the suffix in the setter name as well
                let mut s = String::with_capacity(head.len() + 2);
                s.push_str(head);
                s.push_str("<<");
                s
            };
            let setter_ba =
                ctx.vm.intern_string(setter_name.as_str(), ctx.heap);
            let setter_tagged: Tagged<ByteArray> = setter_ba.into();
            slot_descs.push(SlotDescriptor::new(
                setter_tagged,
                SlotTags::ASSIGNMENT,
                offset_value,
            ));
        } else {
            slot_descs.push(SlotDescriptor::new(name_tagged, tags, init_value));
        }

        if matches!(ended_by, InitEnd::ObjEnd) {
            break;
        }
    }

    let map = ctx.heap.allocate_slots_map(&slot_descs);
    let obj = ctx.heap.allocate_slots(map, assignable_inits.as_slice());
    outer_accum.push(obj.into(), ctx.heap, &ctx.vm.shared);
    ctx.outputs[0] = outer_accum.into();
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

    let mut inputs = Vector::new(ctx.heap, &ctx.vm.shared, 0);

    let mut outputs = Vector::new(ctx.heap, &ctx.vm.shared, 0);

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

    // --- Parse optional name, but ALWAYS require an effect "( ... )"
    // Peek one token to decide if a name is present.
    let saved_offset = parser.offset;
    let next_tok = match parser.parse_next() {
        Some(t) => t,
        None => {
            return ExecutionResult::Panic(
                "Parsing Method: Missing effect '(...)'",
            );
        }
    };

    let name = match next_tok {
        ParsedToken::Identifier(t) => {
            let s = parser.get_token_string(t);
            if s == "(" {
                // Name omitted. Rewind so parse_effect_inner sees '('.
                parser.offset = saved_offset;
                ctx.vm.intern_string("", ctx.heap)
            } else {
                // Name present.
                ctx.vm.intern_string(s, ctx.heap)
            }
        }
        _ => {
            return ExecutionResult::Panic(
                "Parsing Method: Expected method name identifier or '(' to start effect",
            );
        }
    };

    // --- Parse effect (always required)
    let (inputs_vec, outputs_vec) = match parse_effect_inner(ctx) {
        Ok(v) => v,
        Err(e) => return ExecutionResult::Panic(e),
    };

    // Convert Vectors to Arrays for Method storage
    // SAFETY: allocating this here
    let inputs_arr = unsafe { ctx.heap.allocate_array(inputs_vec.as_slice()) };
    // SAFETY: allocating this here
    let outputs_arr =
        unsafe { ctx.heap.allocate_array(outputs_vec.as_slice()) };

    // Parse body until ';'
    let body_accum = Vector::new(ctx.heap, &ctx.vm.shared, 100);
    // SAFETY: just created

    let end = ctx.vm.intern_string_message(";", ctx.heap);

    let res = parse_until_inner(ctx, Some(end), body_accum);
    if res != ExecutionResult::Normal {
        return ExecutionResult::Panic("Parsing Method: Parsing body failed!");
    }

    // Compile into a quotation (with effect counts)
    // SAFETY: allocating here
    let body_arr = unsafe { ctx.heap.allocate_array(body_accum.as_slice()) };
    let block = BytecodeCompiler::compile(&ctx.vm.shared, body_arr);
    let code = ctx.vm.shared.code_heap.push(block);

    let effect = ctx
        .heap
        .allocate_effect(inputs_arr.into(), outputs_arr.into());
    let method_map =
        ctx.heap.allocate_method_map(name, code, &[], effect.into());
    let method = ctx.heap.allocate_method_object(method_map);

    accumulator.push(method.into(), ctx.heap, &ctx.vm.shared);

    ctx.outputs[0] = accumulator.into();

    ExecutionResult::Normal
}

// -- array
pub fn parse_complete(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let accumulator = Vector::new(ctx.heap, &ctx.vm.shared, 100);

    let res = parse_until_inner(ctx, None, accumulator);
    if res != ExecutionResult::Normal {
        return ExecutionResult::Panic("Parsing failed!");
    }

    let accumulated = ctx.heap.allocate_array(accumulator.as_slice());

    ctx.outputs[0] = accumulated.as_value_handle();

    ExecutionResult::Normal
}

// TODO: this is not correct, use parse_complete as correct example
// end -- array
pub fn parse_until(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let accumulator = Vector::new(ctx.heap, &ctx.vm.shared, 10);

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
    ctx.outputs[0] = unsafe { accumulated.into() };

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
