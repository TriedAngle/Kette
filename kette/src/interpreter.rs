use crate::{
    Activation, ActivationStack, ActivationType, Allocator, ExecutionState,
    Handle, HeapProxy, Instruction, LookupResult, Message, OpCode,
    PrimitiveMessageIndex, Quotation, Selector, SlotMap, SlotObject, SlotTags,
    ThreadProxy, VMProxy, Value, get_primitive, transmute,
};

#[derive(Debug, Clone)]
pub struct ExecutionContext {
    /// Pointer to the *next* instruction to execute
    pub ip: *const Instruction,
    /// Pointer to the start of the constant pool
    pub cp: *const Value,
    /// The 'self' value for the current frame
    pub receiver: Value,
    /// Pointer to the start of the instructions (needed to calculate index for sync)
    pub inst_base: *const Instruction,
}

#[derive(Debug)]
pub struct Interpreter {
    pub vm: VMProxy,
    pub thread: ThreadProxy,
    pub heap: HeapProxy,
    pub state: ExecutionState,
    pub activations: ActivationStack,
    pub cache: Option<ExecutionContext>,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum NumberError {
    Overflow,
    DivisionByZero,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum ExecutionResult {
    Normal,
    ActivationChanged,
    NumberError(NumberError),
    Yield,
    Panic(&'static str),
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
        }
    }

    pub fn init(&mut self) {}

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

        unsafe {
            let base = inst_slice.as_ptr();
            self.cache = Some(ExecutionContext {
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
    unsafe fn context_unchecked(&self) -> &ExecutionContext {
        unsafe { self.cache.as_ref().unwrap_unchecked() }
    }

    /// Helper to get mutable reference to context in the inner loop.
    /// # Safety
    /// Caller guarantees `reload_context` was called and stack is not empty.
    #[inline(always)]
    unsafe fn context_unchecked_mut(&mut self) -> &mut ExecutionContext {
        unsafe { self.cache.as_mut().unwrap_unchecked() }
    }

    pub fn add_quotation(&mut self, quotation: Handle<Quotation>) {
        let receiver = self
            .current_activation()
            .map(|a| a.object.receiver)
            .unwrap_or(self.vm.specials().false_object.as_value_handle());

        let new =
            self.heap
                .allocate_quotation_activation(receiver, quotation, &[]);
        self.activations
            .new_activation(new, ActivationType::Quotation);
    }

    pub fn add_method(
        &mut self,
        receiver: Handle<Value>,
        method: Handle<SlotObject>,
    ) {
        let map = method.map;

        let slot_count = map.input_count();

        // idea: peek here, this saves the inputs,
        // now just continue with normal stack
        // SAFETY: TODO: stack depth check
        let slots =
            unsafe { self.state.stack_peek_slice_unchecked(slot_count) };
        // SAFETY: TODO: actually put them into handle set
        let slots = unsafe { crate::transmute::values_as_handles(slots) };

        let new = self
            .heap
            .allocate_method_activation(receiver, method, slots);
        self.activations.new_activation(new, ActivationType::Method);
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
        // Initial load
        self.reload_context();

        // Check if we actually have something to run
        if self.activations.is_empty() {
            return ExecutionResult::Normal;
        }

        loop {
            // 1. Run a single instruction
            // SAFETY: We checked is_empty() above, and reload_context() ensures validity.
            let res = unsafe { self.execute_bytecode() };

            // 2. Handle the result
            match res {
                ExecutionResult::Normal => {
                    // Fast path: Just continue looping.
                    // IP was already updated in execute_single_bytecode.
                }
                ExecutionResult::ActivationChanged => {
                    // Method call or Return happened. Pointers are invalid.
                    self.reload_context();
                    // If stack is empty (after main returns), we are done
                    if self.activations.is_empty() {
                        return ExecutionResult::Normal;
                    }
                }
                // Yield, Panic, etc.
                _ => return res,
            }
        }
    }

    /// Same as execute but breaks at depth
    pub fn execute_with_depth(&mut self) -> ExecutionResult {
        self.reload_context();

        // Check if we actually have something to run
        if self.activations.is_empty() {
            return ExecutionResult::Normal;
        }
        let depth = self.activations.depth();

        loop {
            // 1. Run a single instruction
            // SAFETY: We checked is_empty() above, and reload_context() ensures validity.
            let res = unsafe { self.execute_bytecode() };

            // 2. Handle the result
            match res {
                ExecutionResult::Normal => {
                    // Fast path: Just continue looping.
                    // IP was already updated in execute_single_bytecode.
                }
                ExecutionResult::ActivationChanged => {
                    // Method call or Return happened. Pointers are invalid.
                    self.reload_context();
                    // If stack is empty (after main returns), we are done
                    if self.activations.depth() == depth
                        || self.activations.is_empty()
                    {
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
    pub unsafe fn execute_bytecode(&mut self) -> ExecutionResult {
        // 1. Fetch & Advance
        let instruction = {
            // SAFETY: context is initializd
            let ctx = unsafe { self.context_unchecked_mut() };
            ctx.fetch_next_instruction()
        };

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
                // SAFETY: correctly setup by compiler
                let receiver =
                    unsafe { self.state.pop_unchecked().as_handle_unchecked() };
                let res = self.primitive_send(receiver, prim_id);
                self.record_depth();
                res
            }
            OpCode::CreateSlotObject => {
                // SAFETY: correctly setup by compiler
                let map_val =
                    unsafe { self.context_unchecked().fetch_constant(operand) };
                // SAFETY: correctly setup by compiler
                let mut map =
                    unsafe { map_val.as_handle_unchecked().cast::<SlotMap>() };

                self.heap.safepoint();

                let slot_count = map.data_slots();
                // SAFETY: correctly setup by compiler
                let slots =
                    unsafe { self.state.stack_pop_slice_unchecked(slot_count) };
                let slots = map.collect_values(slots);

                let obj = self.heap.allocate_slots(map, &slots);
                self.state.push(obj.into());

                ExecutionResult::ActivationChanged
            }
            OpCode::Return => {
                let _ = self.activations.pop();
                ExecutionResult::ActivationChanged
            }
            // we match others before already
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
        // SAFETY: not safe yet, TOOD: depth check
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
            ExecutionResult::Panic(msg) => panic!("Panic: {:?}", msg),
            _ => unimplemented!(
                "TODO: implement the different ExecutionResult handling"
            ),
        }
        if res != ExecutionResult::Normal {
            outputs
                .into_iter()
                .for_each(|out| self.state.push(out.into()));
        }

        res
    }

    pub fn send(
        &mut self,
        receiver: Handle<Value>,
        selector: Selector,
    ) -> ExecutionResult {
        let selector_name = selector.name.as_utf8();
        let _span = tracing::span!(tracing::Level::TRACE, "send message", receiver = ?receiver, selector = ?selector_name).entered();

        let res = selector.clone().lookup_object(&receiver.inner());

        let slot = match res {
            LookupResult::Found { slot, .. } => slot,
            LookupResult::None => {
                panic!("Panic: {:?} not found", selector_name)
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

            self.add_method(receiver, method);

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
        unsafe {
            let inst = *self.ip;
            self.ip = self.ip.add(1);
            inst
        }
    }

    /// Fetches a value from the constant pool.
    #[inline(always)]
    pub fn fetch_constant(&self, index: u32) -> Value {
        unsafe { *self.cp.add(index as usize) }
    }
}
