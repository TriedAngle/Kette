// TODO: remove this unused
#![allow(unused)]

use std::{mem, ops::Deref};

use crate::{
    Allocator, Array, Block, ByteArray, BytecodeCompiler, ExecutionResult,
    Handle, LookupResult, Message, Object, ObjectType, ParsedToken, Parser,
    PrimitiveContext, PrimitiveMessageIndex, Quotation, Selector,
    SlotDescriptor, SlotObject, SlotTags, Tagged, Value, Vector, get_primitive,
    primitive_index,
};

fn parser_error(ctx: &PrimitiveContext, msg: &str) -> ExecutionResult {
    let parser = unsafe { ctx.receiver.cast::<Parser>() };

    let error_msg = format!(
        "Parsing Error: {} (line {}, col {})",
        msg, parser.line, parser.column
    );

    // TODO: heap alloc this
    let leaked = Box::leak(error_msg.into_boxed_str());
    ExecutionResult::Panic(leaked)
}

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
        ParsedToken::Float((float, _)) => {
            let float = heap.allocate_float(float);
            state.push(float.into());
        }
        ParsedToken::Fixnum((num, _)) => {
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

impl Value {
    #[inline]
    pub fn as_message_handle(self) -> Option<Handle<Message>> {
        if !self.is_object() {
            return None;
        }
        let h = unsafe { self.as_heap_handle_unchecked() };
        if unsafe { h.header.object_type().unwrap_unchecked() }
            == ObjectType::Message
        {
            Some(unsafe { h.cast::<Message>() })
        } else {
            None
        }
    }
}

pub fn parse_object(ctx: &mut PrimitiveContext) -> ExecutionResult {
    // SAFETY: must exist by contract (outer accumulator)
    let mut outer_accum = unsafe { ctx.inputs[0].cast::<Vector>() };

    #[inline]
    fn message_name<'a>(v: Value) -> Option<&'a str> {
        if !v.is_object() {
            return None;
        }
        let h = unsafe { v.as_heap_handle_unchecked() };
        let ty = unsafe { h.header.object_type().unwrap_unchecked() };
        if ty != ObjectType::Message {
            return None;
        }
        let msg = unsafe { h.cast::<Message>() };
        let ba = unsafe { msg.value.promote_to_handle() };
        Some(unsafe {
            mem::transmute::<&'_ str, &'a str>(
                ba.as_utf8().expect("must exist"),
            )
        })
    }

    // Helper to check if a value matches a specific message handle
    #[inline]
    fn is_message(v: Value, msg: Handle<Message>) -> bool {
        if !v.is_object() {
            return false;
        }
        let h = unsafe { v.as_heap_handle_unchecked() };
        if unsafe { h.header.object_type().unwrap_unchecked() }
            != ObjectType::Message
        {
            return false;
        }
        unsafe { h.cast::<Message>() == msg }
    }

    let dot_msg = ctx.vm.intern_string_message(".", ctx.heap);
    let pipe_msg = ctx.vm.intern_string_message("|", ctx.heap);
    let dash_msg = ctx.vm.intern_string_message("--", ctx.heap);
    let end_msg = ctx.vm.intern_string_message("|)", ctx.heap);

    let mut slot_descs: Vec<SlotDescriptor> = Vec::new();
    let mut assignable_inits: Vec<Value> = Vec::new();
    let mut assignable_offset: i64 = 0;

    let mut inputs_count: u32 = 0;
    let mut outputs_count: u32 = 0;
    let mut reading_inputs = true;
    let mut saw_separator = false;
    let mut has_code = false;

    // Expression Parser (Local Closure)
    let mut parse_and_eval_slot = |ctx: &mut PrimitiveContext| -> Result<
        (Value, Handle<Message>),
        &'static str,
    > {
        let mut accum = Vector::new(ctx.heap, &ctx.vm.shared, 8);
        let terminator_found: Handle<Message>;

        loop {
            // 1. Get Token
            let res = parse_next(ctx);
            if res != ExecutionResult::Normal {
                return Err("Parsing Object: Internal parser error");
            }
            let next = unsafe { ctx.state.pop_unchecked() };

            if next == ctx.vm.shared.specials.false_object.as_value() {
                return Err("Parsing Object: Unexpected EOF in slot value");
            }

            // Check Terminator
            if let Some(msg_handle) = next.as_message_handle() {
                if msg_handle == dot_msg
                    || msg_handle == pipe_msg
                    || msg_handle == dash_msg
                    || msg_handle == end_msg
                {
                    terminator_found = msg_handle;
                    break;
                }
            }

            if let Some(msg) = next.as_message_handle() {
                let parsers = ctx.vm.specials().parsers;
                let name = unsafe { msg.value.promote_to_handle() };
                let selector = Selector::new(name, ctx.vm.shared.clone());

                match selector.lookup_object(&parsers.as_value()) {
                    LookupResult::Found { slot, .. } => {
                        let tags = slot.tags();
                        if tags.contains(SlotTags::EXECUTABLE) {
                            // Execute parser word
                            let exec_res = if tags.contains(SlotTags::PRIMITIVE)
                            {
                                let id = slot
                                    .value
                                    .as_tagged_fixnum::<usize>()
                                    .unwrap();
                                let idx = unsafe {
                                    PrimitiveMessageIndex::from_usize(id.into())
                                };
                                ctx.state.push(accum.as_value());
                                ctx.interpreter
                                    .primitive_send(ctx.receiver, idx)
                            } else {
                                let method = unsafe {
                                    slot.value.as_heap_handle_unchecked().cast()
                                };
                                ctx.state.push(accum.as_value());
                                ctx.interpreter
                                    .add_method(ctx.receiver, method);
                                ctx.interpreter.execute_with_depth()
                            };

                            if exec_res != ExecutionResult::Normal {
                                return Err(
                                    "Parsing Object: Error executing parser word",
                                );
                            }

                            // Restore accum from stack (parser protocol: accum -- accum)
                            let new_accum_val =
                                unsafe { ctx.state.pop().unwrap() };
                            // SAFETY: assume parser kept the type correct
                            let new_accum = unsafe {
                                new_accum_val
                                    .as_handle_unchecked()
                                    .cast::<Vector>()
                            };
                            accum = new_accum;
                        } else {
                            // Non-executable in parser namespace -> treat as data
                            accum.push(slot.value, ctx.heap, &ctx.vm.shared);
                        }
                    }
                    LookupResult::None => {
                        accum.push(next, ctx.heap, &ctx.vm.shared);
                    }
                }
            } else {
                // Not a message, just push
                accum.push(next, ctx.heap, &ctx.vm.shared);
            }
        }

        // Compile & Execute the collected tokens
        let expr_slice = accum.as_slice();
        if expr_slice.is_empty() {
            return Err("Parsing Object: Empty slot initializer");
        }

        let arr = ctx.heap.allocate_array(expr_slice);
        let block = BytecodeCompiler::compile(&ctx.vm.shared, arr);
        let code = ctx.vm.shared.code_heap.push(block);
        let quot = ctx.heap.allocate_quotation(arr, code, 0, 0);

        let depth_before = ctx.state.depth;
        ctx.interpreter.add_quotation(quot);
        let exec_res = ctx.interpreter.execute_with_depth();

        if exec_res != ExecutionResult::Normal {
            return Err("Parsing Object: Slot initializer execution failed");
        }

        let depth_after = ctx.state.depth;
        if depth_after != depth_before + 1 {
            return Err(
                "Parsing Object: Slot initializer must yield exactly one value",
            );
        }

        Ok((unsafe { ctx.state.pop_unchecked() }, terminator_found))
    };

    // Main Parsing Loop
    loop {
        // --- 1. Parse Slot Name ---
        let _ = parse_next(ctx);
        let token_val = unsafe { ctx.state.pop_unchecked() };

        if token_val == ctx.vm.shared.specials.false_object.as_value() {
            return parser_error(ctx, "Unterminated object (EOF)");
        }

        if let Some(msg) = token_val.as_message_handle() {
            if msg == end_msg {
                break;
            }
            if msg == pipe_msg {
                has_code = true;
                break;
            }
            if msg == dash_msg {
                if saw_separator {
                    if saw_separator {
                        return parser_error(ctx, "Duplicate separator '--'");
                    }
                }
                saw_separator = true;
                reading_inputs = false;
                continue;
            }
        }

        // It's a real slot name
        let Some(token_str) = message_name(token_val) else {
            return parser_error(ctx, "Expected slot name or terminator");
        };

        let raw_name = token_str;
        let is_potential_parent = raw_name.ends_with('*');
        let name_ba = ctx.vm.intern_string(raw_name, ctx.heap);
        let name_tagged: Tagged<ByteArray> = name_ba.into();
        let mut tags = SlotTags::empty();

        let _ = parse_next(ctx);
        let op_val = unsafe { ctx.state.pop_unchecked() };

        let Some(op_str) = message_name(op_val) else {
            return parser_error(ctx, "Expected operator after slot name");
        };

        // Determine type of declaration
        let op_msg = op_val.as_message_handle().unwrap(); // safe because message_name verified it

        let is_terminator_op = op_msg == dot_msg
            || op_msg == end_msg
            || op_msg == pipe_msg
            || op_msg == dash_msg;

        let init_val: Value;
        let terminator: Handle<Message>;
        let is_assignable: bool;

        if is_terminator_op {
            is_assignable = true;
            init_val = ctx.vm.shared.specials.false_object.as_value();
            terminator = op_msg;
        } else {
            is_assignable = match op_str {
                ":=" => true,
                "=" => false,
                _ => {
                    return parser_error(
                        ctx,
                        &format!("Invalid operator '{}'", op_str),
                    );
                }
            };

            match parse_and_eval_slot(ctx) {
                Ok((val, term)) => {
                    init_val = val;
                    terminator = term;
                }
                Err(e) => return parser_error(ctx, e),
            }
        }

        // Register Slot
        if is_assignable {
            tags |= SlotTags::ASSIGNABLE;
            if is_potential_parent {
                tags |= SlotTags::PARENT;
            }

            let offset_val = Value::from_fixnum(assignable_offset);
            assignable_offset += 1;

            slot_descs.push(SlotDescriptor::new(name_tagged, tags, offset_val));
            assignable_inits.push(init_val);

            // Setter `name<<`
            let mut s = String::with_capacity(raw_name.len() + 2);
            s.push_str(raw_name);
            s.push_str("<<");
            let setter_ba = ctx.vm.intern_string(&s, ctx.heap);
            slot_descs.push(SlotDescriptor::new(
                setter_ba.into(),
                SlotTags::ASSIGNMENT,
                offset_val,
            ));

            if reading_inputs {
                inputs_count += 1;
            } else {
                outputs_count += 1;
            }
        } else {
            // Constant Slot
            if init_val.is_object() {
                let h = unsafe { init_val.as_heap_handle_unchecked() };
                if let Some(slot) = h.downcast_ref::<SlotObject>() {
                    let map = unsafe { slot.map.promote_to_handle() };
                    let ptr: usize = map.code.into();
                    if ptr != 0 {
                        tags |= SlotTags::EXECUTABLE;
                    };
                    if is_potential_parent {
                        tags |= SlotTags::PARENT;
                    }
                }
            } else if is_potential_parent {
                tags |= SlotTags::PARENT;
            }
            slot_descs.push(SlotDescriptor::new(name_tagged, tags, init_val));
        }

        // Terminators
        if terminator == dot_msg {
            continue;
        } else if terminator == end_msg {
            break;
        } else if terminator == pipe_msg {
            has_code = true;
            break;
        } else if terminator == dash_msg {
            if saw_separator {
                return parser_error(ctx, "Duplicate separator '--'");
            }
            saw_separator = true;
            reading_inputs = false;
            continue;
        }
    }

    // Parse Code Body if existant
    let code_ptr: usize = if has_code {
        let code_accum = Vector::new(ctx.heap, &ctx.vm.shared, 100);
        // We use parse_until_inner logic here looking for `)`
        // Note: The previous loop stopped at `|`.
        let closing_paren = ctx.vm.intern_string_message(")", ctx.heap);

        let res = parse_until_inner(ctx, Some(closing_paren), code_accum);
        if res != ExecutionResult::Normal {
            return parser_error(ctx, "Failed to parse code body");
        }

        let body_arr =
            unsafe { ctx.heap.allocate_array(code_accum.as_slice()) };
        let block = BytecodeCompiler::compile(&ctx.vm.shared, body_arr);
        let code_handle = ctx.vm.shared.code_heap.push(block);
        code_handle as *const Block as usize
    } else {
        0
    };

    // Construct Object
    let effect: u64 = if saw_separator || has_code {
        ((inputs_count as u64) << 32) | (outputs_count as u64)
    } else {
        0
    };

    let map = ctx.heap.allocate_slots_map(
        &slot_descs,
        code_ptr.into(),
        effect.into(),
    );
    let obj = ctx.heap.allocate_slots(map, assignable_inits.as_slice());

    outer_accum.push(obj.into(), ctx.heap, &ctx.vm.shared);
    ctx.outputs[0] = outer_accum.into();

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
                                .cast::<SlotObject>()
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
