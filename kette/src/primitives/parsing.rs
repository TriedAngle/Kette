use crate::{
    Allocator, BytecodeCompiler, ExecutionResult, Handle, LookupResult,
    Message, ObjectType, ParsedToken, Parser, PrimitiveContext,
    PrimitiveMessageIndex, Selector, SlotDescriptor, SlotObject, SlotTags,
    Value, Vector,
};

fn parser_error(ctx: &PrimitiveContext, msg: &str) -> ExecutionResult {
    // SAFETY: must be parser
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

    let (res, _) = parse_until_inner(ctx, &[end], body_accum);
    if res != ExecutionResult::Normal {
        return ExecutionResult::Panic("Parsing failed!");
    }

    let body = ctx.heap.allocate_array(body_accum.as_slice());
    let code = BytecodeCompiler::compile(&ctx.vm.shared, ctx.heap, body);
    // TODO: this must be updated
    let quotation = ctx.heap.allocate_quotation(code, 0, 0);
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
        // SAFETY: checked
        let h = unsafe { self.as_heap_handle_unchecked() };
        // SAFETY: checked
        if unsafe { h.header.object_type().unwrap_unchecked() }
            == ObjectType::Message
        {
            // SAFETY: checked
            Some(unsafe { h.cast::<Message>() })
        } else {
            None
        }
    }
}

// -- array
pub fn parse_complete(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let accumulator = Vector::new(ctx.heap, &ctx.vm.shared, 100);

    let (res, _) = parse_until_inner(ctx, &[], accumulator);
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

    let (res, _) = parse_until_inner(ctx, &[end], accumulator);
    if res != ExecutionResult::Normal {
        return ExecutionResult::Panic("Parsing failed!");
    }

    // trimming
    let accumulated = ctx.heap.allocate_array(accumulator.as_slice());
    ctx.outputs[0] = accumulated.into();

    ExecutionResult::Normal
}

fn parse_until_inner<'m, 'ex, 'arg>(
    ctx: &'m mut PrimitiveContext<'ex, 'arg>,
    ends: &[Handle<Message>],
    mut accum: Handle<Vector>,
) -> (ExecutionResult, Option<Handle<Message>>) {
    // SAFETY: this is safe
    let _parser = unsafe { ctx.receiver.cast::<Parser>() };

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

        if ends.contains(&message) {
            return (ExecutionResult::Normal, Some(message));
        }

        let parsers = ctx.vm.specials().parsers;

        let name = message.value;
        let selector = Selector::new(name, ctx.vm.shared.clone());
        let lookup = selector.lookup_object(&parsers.as_value());

        match lookup {
            LookupResult::Found {
                object: _,
                slot,
                slot_index: _,
            } => {
                let tags = slot.tags();

                if tags.contains(SlotTags::PRIMITIVE) {
                    let id = slot
                        .value
                        .as_tagged_fixnum::<usize>()
                        .expect("primitive must have fixnum");

                    // SAFETY: must store valid primitive idx if primitive executable
                    let message_idx =
                        unsafe { PrimitiveMessageIndex::from_usize(id.into()) };

                    ctx.state.push(accum.as_value());
                    ctx.interpreter.primitive_send(ctx.receiver, message_idx);

                    // SAFETY: this is safe
                    accum = unsafe {
                        ctx.state
                            .pop()
                            .expect("must exist")
                            .as_handle_unchecked()
                            .cast()
                    };
                    continue;
                } else {
                    let should_execute_method = if slot.value.is_object() {
                        let h =
                            // SAFETY: this is safe
                            unsafe { slot.value.as_heap_handle_unchecked() };
                        if let Some(slot_obj) = h.downcast_ref::<SlotObject>() {
                            slot_obj.map.has_code()
                        } else {
                            false
                        }
                    } else {
                        false
                    };

                    if should_execute_method {
                        // SAFETY: this is safe
                        let method = unsafe {
                            slot.value
                                .as_heap_handle_unchecked()
                                .cast::<SlotObject>()
                        };

                        ctx.state.push(accum.as_value());
                        ctx.interpreter.add_method(ctx.receiver, method);

                        let exec_res =
                            ctx.interpreter.execute_current_activation();

                        if exec_res != ExecutionResult::Normal {
                            println!("error");
                            return (exec_res, None);
                        }

                        // SAFETY: this is safe
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
            }
            LookupResult::None => accum.push(next, ctx.heap, &ctx.vm.shared),
        }
    }

    if !ends.is_empty() {
        return (ExecutionResult::Panic("not found"), None);
    }
    (ExecutionResult::Normal, None)
}

pub fn parse_object(ctx: &mut PrimitiveContext) -> ExecutionResult {
    // SAFETY: must exist by contract (outer accumulator)
    let mut outer_accum = unsafe { ctx.inputs[0].cast::<Vector>() };
    let heap = &mut ctx.heap;

    // --- Intern Common Messages ---
    let dot_msg = ctx.vm.intern_string_message(".", heap);
    let pipe_msg = ctx.vm.intern_string_message("|", heap);
    let dash_msg = ctx.vm.intern_string_message("--", heap);
    let close_paren_msg = ctx.vm.intern_string_message(")", heap);
    let close_bar_msg = ctx.vm.intern_string_message("|)", heap);
    let create_obj_msg = ctx.vm.specials().message_create_object;

    // Default value for implicit slots (e.g. `x .` or `x |`)
    let false_val = ctx.vm.shared.specials.false_object.as_value();

    // Terminators for the value parser
    let value_terminators = [dot_msg, dash_msg, pipe_msg, close_bar_msg];
    // Terminators for the code body parser
    let body_terminators = [close_bar_msg, close_paren_msg];

    // --- State ---
    let mut slot_descs: Vec<SlotDescriptor> = Vec::new();
    let mut assignable_offset: i64 = 0;

    let mut has_code = false;
    let mut saw_separator = false;
    let mut reading_inputs = true;
    let mut inputs_count: u32 = 0;
    let mut outputs_count: u32 = 0;

    loop {
        // 1. Peek/Parse next token (Name or Terminator)
        let res = parse_next(ctx);
        if res != ExecutionResult::Normal {
            return res;
        }

        // SAFETY: this is safe
        let token_val = unsafe { ctx.state.pop_unchecked() };

        // Handle EOF
        if token_val == false_val {
            return parser_error(ctx, "Unterminated object (EOF)");
        }

        // Check for Object Terminators/Separators at the start of a slot definition
        if let Some(msg) = token_val.as_message_handle() {
            if msg == close_bar_msg || msg == close_paren_msg {
                break;
            }
            if msg == pipe_msg {
                has_code = true;
                break;
            }
            if msg == dash_msg {
                if saw_separator {
                    return parser_error(ctx, "Duplicate separator '--'");
                }
                saw_separator = true;
                reading_inputs = false;
                continue;
            }
            if msg == dot_msg {
                continue; // Skip stray dots
            }
        }

        // 2. Parse Slot Name
        let name_msg = match token_val.as_message_handle() {
            Some(m) => m,
            None => return parser_error(ctx, "Expected slot name"),
        };

        // SAFETY: Message value guaranteed to be valid UTF8 ByteArray by VM invariants
        let raw_name_str = name_msg.value.as_utf8().expect("valid utf8");

        let is_parent = raw_name_str.ends_with('*');
        // Intern name (stripping * if needed usually handled here or we just intern raw)
        // Assuming we keep strict name correspondence:
        let name_ba = ctx.vm.intern_string(raw_name_str, ctx.heap);

        // 3. Parse Operator OR Implicit Terminator
        let res = parse_next(ctx);
        if res != ExecutionResult::Normal {
            return res;
        }
        // SAFETY: this is safe
        let op_val = unsafe { ctx.state.pop_unchecked() };

        let op_msg = op_val
            .as_message_handle()
            .ok_or("Expected operator or terminator after slot name")
            .map_err(|e| parser_error(ctx, e))
            .expect("get message");

        let terminator: Handle<Message>;
        let is_assignable: bool;

        // Check if the "operator" is actually a terminator (Implicit Assignment)
        // Covers: `name .`, `name --`, `name |`, `name |)`
        if value_terminators.contains(&op_msg) {
            // Implicit: name := false
            outer_accum.push(false_val, ctx.heap, &ctx.vm.shared);
            terminator = op_msg;
            is_assignable = true; // Implicit slots are assignable
        } else {
            // Explicit: name = val ... or name := val ...
            let op_str = op_msg.value.as_utf8().expect("valid utf8");

            is_assignable = match op_str {
                "=" => false,
                ":=" => true,
                _ => {
                    return parser_error(
                        ctx,
                        &format!("Unknown operator {}", op_str),
                    );
                }
            };

            // Parse Value Stream
            let (res, term_opt) =
                parse_until_inner(ctx, &value_terminators, outer_accum);
            if res != ExecutionResult::Normal {
                return res;
            }

            // parse_until_inner panics if no terminator found, so unwrap is safe
            terminator = term_opt.expect("get terminator");
        }

        // 4. Register Descriptor
        let mut tags = SlotTags::empty();
        if is_parent {
            tags |= SlotTags::PARENT;
        }

        if is_assignable {
            tags |= SlotTags::ASSIGNABLE;
            let offset_val = Value::from_fixnum(assignable_offset);
            assignable_offset += 1;

            slot_descs.push(SlotDescriptor::new(name_ba, tags, offset_val));

            // Generate Setter: name<<
            let mut s = String::with_capacity(raw_name_str.len() + 2);
            s.push_str(raw_name_str);
            s.push_str("<<");
            let setter_ba = ctx.vm.intern_string(&s, ctx.heap);

            slot_descs.push(SlotDescriptor::new(
                setter_ba,
                SlotTags::ASSIGNMENT,
                offset_val,
            ));

            if reading_inputs {
                inputs_count += 1;
            } else {
                outputs_count += 1;
            }
        } else {
            slot_descs.push(SlotDescriptor::new(name_ba, tags, false_val));
        }

        if terminator == dot_msg {
            continue;
        } else if terminator == dash_msg {
            if saw_separator {
                return parser_error(ctx, "Duplicate separator '--'");
            }
            saw_separator = true;
            reading_inputs = false;
            continue;
        } else if terminator == pipe_msg {
            has_code = true;
            break;
        } else if terminator == close_bar_msg {
            break;
        }
    }

    let code = if has_code {
        let code_accum = Vector::new(ctx.heap, &ctx.vm.shared, 64);

        let (res, _) = parse_until_inner(ctx, &body_terminators, code_accum);
        if res != ExecutionResult::Normal {
            return parser_error(ctx, "Failed to parse code body");
        }

        let body = ctx.heap.allocate_array(code_accum.as_slice());
        BytecodeCompiler::compile(&ctx.vm.shared, ctx.heap, body)
    } else {
        // SAFETY: this is safe by the protocol
        unsafe { Handle::null() }
    };

    let effect = ((inputs_count as u64) << 32) | (outputs_count as u64);

    let map = ctx
        .heap
        .allocate_slots_map(&slot_descs, code, effect.into());

    outer_accum.push(map.into(), ctx.heap, &ctx.vm.shared);
    outer_accum.push(create_obj_msg.as_value(), ctx.heap, &ctx.vm.shared);

    ctx.outputs[0] = outer_accum.into();
    ExecutionResult::Normal
}

// TODO: these should be moved into unserspace
pub fn parse_line_comment(ctx: &mut PrimitiveContext) -> ExecutionResult {
    // SAFETY: must be parser, can't be called otherwise
    let mut parser = unsafe { ctx.receiver.cast::<Parser>() };
    // SAFETY: must exist by contract
    let accumulator = unsafe { ctx.inputs[0].cast::<Vector>() };

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
