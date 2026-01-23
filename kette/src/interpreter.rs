use std::{fmt, io::{self, Write}};

use crate::{
    Activation, ActivationObject, ActivationStack, ActivationType, Allocator,
    ExecutionState, Handle, HeapProxy, Instruction, LookupResult, Message,
    OpCode, PrimitiveMessageIndex, Quotation, Selector, SlotMap, SlotObject,
    SlotTags, ThreadProxy, VMProxy, Value, get_primitive, transmute,
};

#[derive(Debug, Clone)]
pub struct ExecutionContext {
    /// the activation we are woking on right now
    pub activation: Handle<ActivationObject>,
    /// Pointer to the *next* instruction to execute
    pub ip: *const Instruction,
    /// Pointer to the start of the constant pool
    pub cp: *const Value,
    /// The 'self' value for the current frame
    pub receiver: Value,
    /// Pointer to the start of the instructions (needed to calculate index for sync)
    pub inst_base: *const Instruction,
}

pub struct Interpreter {
    pub vm: VMProxy,
    pub thread: ThreadProxy,
    pub heap: HeapProxy,
    pub state: ExecutionState,
    pub activations: ActivationStack,
    pub cache: Option<ExecutionContext>,
    pub output: Box<dyn Write>,
}

impl fmt::Debug for Interpreter {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Interpreter")
            .field("vm", &self.vm)
            .field("thread", &self.thread)
            .field("heap", &self.heap)
            .field("state", &self.state)
            .field("activations", &self.activations)
            .field("cache", &self.cache)
            .field("output", &"<output stream>") // Placeholder string
            .finish()
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum NumberError {
    Overflow,
    DivisionByZero,
}

#[derive(Debug, Clone, PartialEq, Eq)] // Removed Copy
pub enum ExecutionResult {
    Normal,
    ActivationChanged,
    NumberError(NumberError),
    Yield,
    Panic(String),
}

impl Interpreter {
    pub fn new(
        vm: VMProxy,
        thread: ThreadProxy,
        heap: HeapProxy,
        state: ExecutionState,
    ) -> Self {
        Self {
            vm,
            thread,
            heap,
            state,
            activations: ActivationStack::new(),
            cache: None,
            output: Box::new(io::stdout()),
        }
    }

    pub fn set_output(&mut self, output: Box<dyn Write>) {
        self.output = output;
    }

    #[inline(always)]
    pub fn current_activation(&self) -> Option<&Activation> {
        self.activations.current()
    }

    #[inline(always)]
    pub fn current_activation_mut(&mut self) -> Option<&mut Activation> {
        self.activations.current_mut()
    }

    #[inline(always)]
    pub fn increment_instruction(&mut self) {
        if let Some(activation) = self.current_activation_mut() {
            activation.index += 1
        };
    }

    #[inline(always)]
    pub fn current_instruction(&mut self) -> Option<Instruction> {
        if let Some(activation) = self.current_activation() {
            let index = activation.index;
            let code = activation.code();
            // SAFETY: this is safe
            let instructions = code.instructions();
            return Some(instructions[index]);
        }
        None
    }

    #[inline(always)]
    pub fn sync_context(&mut self) {
        // We only sync if we have a valid cache
        if let Some(ctx) = &self.cache {
            // SAFETY: We assume activations.current() matches the cache.
            // If cache exists, activation must exist.
            if let Some(activation) = self.activations.current_mut() {
                // Calculate the index based on pointer offset
                // SAFETY: ip and inst_base are derived from the same Code object slice
                let index = unsafe { ctx.ip.offset_from(ctx.inst_base) };
                activation.index = index as usize;
            }
        }
    }

    /// Rebuilds the execution cache from the top of the ActivationStack.
    /// Call this after pushing a new frame, returning, or after GC moves objects.
    #[inline(always)]
    pub fn reload_context(&mut self) {
        let Some(activation) = self.activations.current() else {
            self.cache = None;
            return;
        };

        let code = activation.code();
        let receiver = activation.object.receiver.as_value();

        // SAFETY: We are taking raw pointers to the HeapObject data.
        // These are valid until the next safepoint/allocation.
        let inst_slice = code.instructions();
        let const_slice = code.constants();

        // SAFETY: this is safe
        unsafe {
            let base = inst_slice.as_ptr();
            self.cache = Some(ExecutionContext {
                activation: activation.object,
                inst_base: base,
                // Resume from where the activation says we are
                ip: base.add(activation.index),
                cp: const_slice.as_ptr(),
                receiver,
            });
        }
    }

    /// Helper to get the context in the inner loop without Option checks.
    /// # Safety
    /// Caller guarantees `reload_context` was called and stack is not empty.
    #[inline(always)]
    pub unsafe fn context_unchecked(&self) -> &ExecutionContext {
        // SAFETY: safe if contract holds
        unsafe { self.cache.as_ref().unwrap_unchecked() }
    }

    /// Helper to get mutable reference to context in the inner loop.
    /// # Safety
    /// Caller guarantees `reload_context` was called and stack is not empty.
    #[inline(always)]
    pub unsafe fn context_unchecked_mut(&mut self) -> &mut ExecutionContext {
        // SAFETY: safe if contract holds
        unsafe { self.cache.as_mut().unwrap_unchecked() }
    }

    #[inline(always)]
    pub fn check_min_stack(&self, count: usize) -> Result<(), ExecutionResult> {
        if self.state.depth < count {
            return Err(ExecutionResult::Panic(format!(
                "Stack Underflow: required {}, got {}",
                count, self.state.depth
            )));
        }
        Ok(())
    }

    pub fn add_quotation(&mut self, quotation: Handle<Quotation>) {
        let activation_object =
            self.heap.allocate_quotation_activation(quotation, &[]);

        self.activations
            .new_activation(activation_object, ActivationType::Quotation);
    }

    pub fn add_method(
        &mut self,
        receiver: Handle<Value>,
        method: Handle<SlotObject>,
    ) -> Result<(), ExecutionResult> {
        let map = method.map;

        let slot_count = map.input_count();

        if let Err(e) = self.check_min_stack(slot_count) {
            return Err(e);
        }

        // idea: peek here, this saves the inputs,
        // now just continue with normal stack
        let slots =
            unsafe { self.state.stack_peek_slice_unchecked(slot_count) };
        // SAFETY: TODO: actually put them into handle set
        let slots = unsafe { crate::transmute::values_as_handles(slots) };

        let new = self
            .heap
            .allocate_method_activation(receiver, method, slots);
        self.activations.new_activation(new, ActivationType::Method);
        Ok(())
    }

    pub fn push_handler(&mut self, tag: Handle<Value>, handler: Handle<Value>) {
        self.activations.push_handler(tag, handler);
    }

    /// Signals an exception.
    pub fn signal_exception(
        &mut self,
        exception: Handle<Value>,
    ) -> ExecutionResult {
        if let Some((activation, handler)) =
            self.activations.find_handler(exception)
        {
            // Push arguments for the handler: ( activation error -- ... )
            self.state.push(activation.as_value());
            self.state.push(exception.into());

            // Execute the handler (Quotation)
            // SAFETY: Checked in primitive
            let quotation = unsafe { handler.cast::<Quotation>() };
            self.add_quotation(quotation);

            return ExecutionResult::ActivationChanged;
        }

        ExecutionResult::Panic("Unhandled Exception".to_string())
    }

    /// unwinds to the target activation.
    pub fn unwind_to(
        &mut self,
        target_activation: Handle<ActivationObject>,
    ) -> ExecutionResult {
        // Read the index we stored as a fixnum
        let index = target_activation.stack_index.into();
        let current_depth = self.activations.depth();

        // Safety checks
        if index >= current_depth {
            return ExecutionResult::Panic(
                "Cannot unwind to a future or current frame".to_string(),
            );
        }

        tracing::debug!(target: "interpreter", "Unwinding from {} to {}", current_depth, index);

        self.activations.unwind_to(index);

        ExecutionResult::ActivationChanged
    }

    /// Helper to retrieve a value from the current code's constant pool
    #[inline(always)]
    pub fn get_constant(&self, index: u32) -> Value {
        // SAFETY: The compiler guarantees the index is within bounds of the allocated Code object.
        unsafe { self.current_activation().unwrap_unchecked() }
            .code()
            .constants()[index as usize]
    }

    /// The Main Execution Loop
    pub fn execute(&mut self) -> ExecutionResult {
        // Run until depth < 1 (aka 0)
        self.execute_until_depth(1)
    }

    pub fn execute_current_activation(&mut self) -> ExecutionResult {
        let depth = self.activations.depth();
        self.execute_until_depth(depth)
    }

    /// Executes the interpreter loop until the stack depth drops below `target_depth`.
    pub fn execute_until_depth(
        &mut self,
        target_depth: usize,
    ) -> ExecutionResult {
        // Initialize Cache
        self.reload_context();

        if self.activations.depth() < target_depth {
            return ExecutionResult::Normal;
        }

        loop {
            let instruction = {
                // SAFETY: context is initializd
                let ctx = unsafe { self.context_unchecked_mut() };
                ctx.fetch_next_instruction()
            };
            // SAFETY: context just initalized
            let res = unsafe { self.execute_bytecode(instruction) };

            match res {
                ExecutionResult::Normal => {
                    // Continue looping.
                    // Depth cannot change in Normal result, so no check needed.
                }
                ExecutionResult::ActivationChanged => {
                    self.reload_context();

                    if self.activations.depth() < target_depth {
                        return ExecutionResult::Normal;
                    }

                    if self.activations.is_empty() {
                        return ExecutionResult::Normal;
                    }
                }
                _ => return res,
            }
        }
    }

    /// # Safety
    /// context must be correctly initialized before
    #[inline(always)]
    pub unsafe fn execute_bytecode(
        &mut self,
        instruction: Instruction,
    ) -> ExecutionResult {
        let op = instruction.opcode();

        // --- FAST PATHS ---
        match op {
            OpCode::PushConstant => {
                // SAFETY: setup correctly by compiler
                let ctx = unsafe { self.context_unchecked() };
                let val = ctx.fetch_constant(instruction.operand());
                self.state.push(val);
                ExecutionResult::Normal
            }
            OpCode::PushSelf => {
                // SAFETY: setup correctly by compiler
                let ctx = unsafe { self.context_unchecked() };
                self.state.push(ctx.receiver);
                ExecutionResult::Normal
            }
            OpCode::PushSmallInteger => {
                let val = instruction.signed_operand() as i64;
                self.state.push(val.into());
                ExecutionResult::Normal
            }
            OpCode::PushReturn => {
                // SAFETY: setup correctly by compiler
                let value = unsafe { self.state.pop_unchecked() };
                self.state.push_return(value);
                ExecutionResult::Normal
            }
            OpCode::PopReturn => {
                // SAFETY: setup correctly by compiler
                let value = unsafe { self.state.pop_return_unchecked() };
                self.state.push(value);
                ExecutionResult::Normal
            }

            // --- SLOW PATHS ---
            // Pass instruction to slow handler.
            // SAFETY: context is initialized
            _ => unsafe { self.execute_bytecode_slow(instruction) },
        }
    }

    /// # Safety
    /// context must be correctly initialized before
    #[inline(never)]
    unsafe fn execute_bytecode_slow(
        &mut self,
        instruction: Instruction,
    ) -> ExecutionResult {
        // Sync the local IP back to the heap object before doing anything dangerous
        self.sync_context();

        let op = instruction.opcode();
        let operand = instruction.operand();

        match op {
            OpCode::Send => {
                // We can use the context helper here too
                let message_val =
                    // SAFETY: correctly setup by compiler
                    unsafe { self.context_unchecked().fetch_constant(operand) };
                let message =
                    // SAFETY: correctly setup by compiler
                    unsafe { message_val.as_handle_unchecked().cast::<Message>() };
                let selector =
                    Selector::new_message(message, self.vm.shared.clone());

                self.heap.safepoint();

                let universe = self.vm.specials().universe;
                let found_receiver = match selector
                    .clone()
                    .lookup_object(&universe.as_value())
                {
                    LookupResult::Found { object, .. } => {
                        // SAFETY: correctly setup by compiler
                        unsafe { object.as_value().as_handle_unchecked() }
                    }
                    LookupResult::None => {
                        if let Err(e) = self.check_min_stack(1) {
                            return e;
                        }
                        // SAFETY: correctly setup by compiler
                        unsafe {
                            self.state.pop_unchecked().as_handle_unchecked()
                        }
                    }
                };

                let res = self.send(found_receiver, selector);
                self.record_depth();
                res
            }
            OpCode::SendPrimitive => {
                let prim_id =
                    // SAFETY: correctly setup by compiler
                    unsafe { PrimitiveMessageIndex::from_usize(operand as usize) };
                self.heap.safepoint();

                if let Err(e) = self.check_min_stack(1) {
                    return e;
                }

                // SAFETY: correctly setup by compiler
                let receiver =
                    unsafe { self.state.pop_unchecked().as_handle_unchecked() };
                let res = self.primitive_send(receiver, prim_id);
                self.record_depth();
                res
            }
            OpCode::CreateSlotObject => {
                self.heap.safepoint();

                // SAFETY: correctly setup by compiler
                let map_val =
                    unsafe { self.context_unchecked().fetch_constant(operand) };
                // SAFETY: correctly setup by compiler
                let mut map =
                    unsafe { map_val.as_handle_unchecked().cast::<SlotMap>() };

                let slot_count = map.data_slots();

                if let Err(e) = self.check_min_stack(slot_count) {
                    return e;
                }

                // SAFETY: correctly setup by compiler
                let slots =
                    unsafe { self.state.stack_pop_slice_unchecked(slot_count) };
                let slots = map.collect_values(slots);

                let obj = self.heap.allocate_slots(map, &slots);
                self.state.push(obj.into());

                ExecutionResult::ActivationChanged
            }
            OpCode::CreateQuotation => {
                self.heap.safepoint();

                // SAFETY: correctly setup by runtime
                let ctx = unsafe { self.context_unchecked() };

                let map_val = ctx.fetch_constant(operand);
                // SAFETY: correctly setup by compiler
                let map =
                    unsafe { map_val.as_handle_unchecked().cast::<SlotMap>() };

                let activation = ctx.activation;

                let quotation = self.heap.allocate_quotation(map, activation);
                self.state.push(quotation.into());

                ExecutionResult::Normal
            }
            OpCode::Return => {
                let _ = self.activations.pop();
                ExecutionResult::ActivationChanged
            }
            // SAFETY: we match others before already
            _ => unsafe { std::hint::unreachable_unchecked() },
        }
    }

    fn record_depth(&self) {
        tracing::info!(target: "interpreter", "stack {}", self.state.depth);
    }

    pub fn primitive_send(
        &mut self,
        receiver: Handle<Value>,
        id: PrimitiveMessageIndex,
    ) -> ExecutionResult {
        let message = get_primitive(id);
        let _span = tracing::span!(tracing::Level::TRACE, "primitive send", receiver = ?receiver, message = ?message.name).entered();

        if let Err(e) = self.check_min_stack(message.inputs) {
            return e;
        }

        let inputs = unsafe { self.state.stack_pop_unchecked(message.inputs) };
        // the initialization is guaranted after the call
        let mut outputs = Vec::with_capacity(message.outputs);

        // SAFETY: gc not running
        let inputs = unsafe { transmute::values_as_handles(inputs.as_slice()) };

        // SAFETY: allocated with this size
        #[allow(clippy::uninit_vec)]
        unsafe {
            outputs.set_len(message.outputs)
        };

        let res = message.call(self, receiver, inputs, &mut outputs);

        match res {
            ExecutionResult::Normal => {
                let outputs = transmute::handles_as_values(outputs.as_slice());

                // SAFETY: not safe in general yet, TODO: size check
                unsafe { self.state.stack_push_slice_unchecked(outputs) };
            }
            ExecutionResult::ActivationChanged => {}
            ExecutionResult::Panic(msg) => return ExecutionResult::Panic(msg),
            _ => unimplemented!(
                "TODO: implement the different ExecutionResult handling"
            ),
        }
        res
    }

    pub fn send(
        &mut self,
        receiver: Handle<Value>,
        selector: Selector,
    ) -> ExecutionResult {
        let selector_name =
            selector.name.as_utf8().expect("Selector must be string");
        let _span = tracing::span!(tracing::Level::TRACE, "send message", receiver = ?receiver, selector = ?selector_name).entered();

        let res = selector.clone().lookup_object(&receiver.inner());

        let slot = match res {
            LookupResult::Found { slot, .. } => slot,
            LookupResult::None => {
                return ExecutionResult::Panic(format!(
                    "Message not understood: '{}'",
                    selector_name
                ));
            }
        };

        if slot.tags().contains(SlotTags::ASSIGNMENT) {
            let offset = slot
                .value
                .as_tagged_fixnum::<usize>()
                .expect("assignment slot must store offset");

            // SAFETY: must be valid by protocol
            // TODO: depth check maybe
            let new_value = unsafe { self.state.pop_unchecked() };

            let recv_val = receiver.inner();
            // SAFETY: must be valid by protocol
            let mut recv_obj = unsafe {
                recv_val.as_heap_handle_unchecked().cast::<SlotObject>()
            };
            // SAFETY: must be valid by protocol
            let val_obj = unsafe { new_value.as_heap_handle_unchecked() };
            self.heap
                .write_barrier(recv_obj.as_heap_value_handle(), val_obj);
            // SAFETY: this is safe
            unsafe { recv_obj.set_slot_unchecked(offset.into(), new_value) };
            return ExecutionResult::Normal;
        }

        if slot.tags().contains(SlotTags::PRIMITIVE) {
            let id = slot
                .value
                .as_tagged_fixnum::<usize>()
                .expect("primitive must have fixnum");
            // Safety: must store valid primitive idx if primitive executable
            let message_idx =
                unsafe { PrimitiveMessageIndex::from_usize(id.into()) };
            // directly execute primitive
            return self.primitive_send(receiver, message_idx);
        }

        if slot.value.is_fixnum() {
            self.state.push(slot.value);
            return ExecutionResult::Normal;
        }

        // SAFETY: must by protocol
        let heap_val = unsafe { slot.value.as_heap_handle_unchecked() };
        if let Some(obj) = heap_val.downcast_ref::<SlotObject>()
            && obj.map.has_code()
        {
            // SAFETY: must by protocol
            let method = unsafe {
                slot.value.as_handle_unchecked().cast::<SlotObject>()
            };

            if let Err(e) = self.add_method(receiver, method) {
                return e;
            }

            return ExecutionResult::ActivationChanged;
        }

        self.state.push(slot.value);
        ExecutionResult::Normal
    }
}

impl ExecutionContext {
    /// Reads the instruction at the current IP and advances the IP.
    #[inline(always)]
    pub fn fetch_next_instruction(&mut self) -> Instruction {
        // SAFETY: execution context is initialized
        unsafe {
            let inst = *self.ip;
            self.ip = self.ip.add(1);
            inst
        }
    }

    /// Fetches a value from the constant pool.
    #[inline(always)]
    pub fn fetch_constant(&self, index: u32) -> Value {
        // SAFETY: execution context is initialized
        unsafe { *self.cp.add(index as usize) }
    }
}
