use std::{
    fmt,
    io::{self, Write},
};

#[cfg(feature = "inline-cache")]
use crate::{Code, FeedbackEntry, HeapValue, ObjectType};

use crate::{
    Activation, ActivationObject, ActivationStack, ActivationType, Allocator,
    Array, BytecodeCompiler, BytecodeWriter, ExecutionState, Handle, HeapProxy,
    LookupResult, Map, Message, OpCode, PrimitiveMessageIndex, Quotation,
    Selector, SlotObject, SlotTags, ThreadProxy, VMProxy, Value, get_primitive,
    transmute,
};

/// Hotness threshold for allocating feedback vectors.
/// A method must be called this many times before IC is enabled.
#[cfg(feature = "inline-cache")]
const IC_HOTNESS_THRESHOLD: usize = 50;

#[derive(Debug, Clone)]
pub struct ExecutionContext {
    /// the activation we are woking on right now
    pub activation: Handle<ActivationObject>,
    /// Pointer to the *next* instruction to execute
    pub ip: *const u8,
    /// Pointer to the start of the constant pool
    pub cp: *const Value,
    /// The 'self' value for the current frame
    pub receiver: Value,
    /// Pointer to the start of the instructions (needed to calculate index for sync)
    pub inst_base: *const u8,
}

/// Bytecode interpreter for executing Kette programs.
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
    #[must_use]
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

    /// Initialize the heap's reference to execution state for GC rooting.
    /// Must be called after the Interpreter is at its final memory location.
    pub fn init_gc_roots(&mut self) {
        self.heap.init_state(&mut self.state, &mut self.activations);
    }

    pub fn set_output(&mut self, output: Box<dyn Write>) {
        self.output = output;
    }

    #[inline(always)]
    #[must_use]
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
    pub fn current_instruction(&mut self) -> Option<OpCode> {
        if let Some(activation) = self.current_activation() {
            let index = activation.index;
            let code = activation.code();
            let instructions = code.instructions();
            // This assumes index points to an opcode.
            if index < instructions.len() {
                return Some(OpCode::from_u8(instructions[index]));
            }
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

        // SAFETY: inst_slice is valid for the lifetime of the cache, derived from Code object.
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
    #[must_use]
    pub unsafe fn context_unchecked(&self) -> &ExecutionContext {
        debug_assert!(
            self.cache.is_some(),
            "context_unchecked called without cache"
        );
        // SAFETY: safe if contract holds
        unsafe { self.cache.as_ref().unwrap_unchecked() }
    }

    /// Helper to get mutable reference to context in the inner loop.
    /// # Safety
    /// Caller guarantees `reload_context` was called and stack is not empty.
    #[inline(always)]
    pub unsafe fn context_unchecked_mut(&mut self) -> &mut ExecutionContext {
        debug_assert!(
            self.cache.is_some(),
            "context_unchecked_mut called without cache"
        );
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

    pub fn add_quotation_with_receiver(
        &mut self,
        quotation: Handle<Quotation>,
        receiver: Handle<Value>,
    ) {
        let activation_object =
            self.heap.allocate_quotation_activation_with_receiver(
                quotation,
                receiver,
                &[],
            );

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

        self.check_min_stack(slot_count)?;

        // SAFETY: stack depth verified above
        let slots =
            unsafe { self.state.stack_peek_slice_unchecked(slot_count) };
        // SAFETY: values are valid handles, no GC between peek and use
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
    #[must_use]
    pub fn get_constant(&self, index: u32) -> Value {
        // SAFETY: The compiler guarantees the index is within bounds of the allocated Code object.
        unsafe { self.current_activation().unwrap_unchecked() }
            .code()
            .constants()[index as usize]
    }

    /// Get the Map for a receiver value.
    /// Returns the traits map for primitives (fixnum, float, etc.) or the
    /// object's map for SlotObjects.
    #[cfg(feature = "inline-cache")]
    #[inline]
    fn get_receiver_map(&self, receiver: Value) -> Option<Handle<Map>> {
        if receiver.is_fixnum() {
            let traits = self.vm.specials().fixnum_traits;
            // SAFETY: traits are SlotObjects
            return Some(unsafe { traits.cast::<SlotObject>() }.map);
        }

        if !receiver.is_object() {
            return None;
        }

        // SAFETY: checked is_object above
        let heap_val = unsafe { receiver.as_heap_handle_unchecked() };

        match heap_val.header.object_type()? {
            ObjectType::Slot => {
                let obj = unsafe { heap_val.cast::<SlotObject>() };
                Some(obj.map)
            }
            ObjectType::Array => {
                let traits = self.vm.specials().array_traits;
                Some(unsafe { traits.cast::<SlotObject>() }.map)
            }
            ObjectType::ByteArray => {
                let traits = self.vm.specials().bytearray_traits;
                Some(unsafe { traits.cast::<SlotObject>() }.map)
            }
            ObjectType::Float => {
                let traits = self.vm.specials().float_traits;
                Some(unsafe { traits.cast::<SlotObject>() }.map)
            }
            ObjectType::BigNum => {
                let traits = self.vm.specials().bignum_traits;
                Some(unsafe { traits.cast::<SlotObject>() }.map)
            }
            ObjectType::Quotation => {
                let traits = self.vm.specials().quotation_traits;
                Some(unsafe { traits.cast::<SlotObject>() }.map)
            }
            ObjectType::Message => {
                let traits = self.vm.specials().message_traits;
                Some(unsafe { traits.cast::<SlotObject>() }.map)
            }
            ObjectType::Alien => {
                let traits = self.vm.specials().alien_traits;
                Some(unsafe { traits.cast::<SlotObject>() }.map)
            }
            _ => None,
        }
    }

    /// Returns the feedback vector if available, None otherwise.
    #[cfg(feature = "inline-cache")]
    fn ensure_feedback_vector(
        &mut self,
        map: Handle<Map>,
        mut code: Handle<Code>,
    ) -> Option<Handle<Array>> {
        // Already allocated?
        if !code.feedback_vector.as_ptr().is_null() {
            return Some(code.feedback_vector);
        }

        // Check hotness threshold
        if map.hotness() < IC_HOTNESS_THRESHOLD {
            return None;
        }

        // No Send sites means no feedback vector needed
        let slot_count = code.feedback_slot_count as usize;
        if slot_count == 0 {
            return None;
        }

        // Allocate feedback vector (1 slot per Send site)
        let sentinel = self.vm.specials().uninitialized_ic_sentinel.as_value();
        let fv = self.heap.allocate_array_fill(slot_count, sentinel);

        // Store in Code (record old -> young edge for GC)
        self.heap.write_barrier(
            code.as_heap_value_handle(),
            fv.as_heap_value_handle(),
        );
        code.feedback_vector = fv;

        Some(fv)
    }

    /// Try to find a cached lookup result in the IC.
    /// Returns (holder, slot_index) on hit, None on miss.
    #[cfg(feature = "inline-cache")]
    fn try_ic_lookup(
        &self,
        fv: &Array,
        feedback_idx: u16,
        receiver_map: Handle<Map>,
    ) -> Option<(Handle<HeapValue>, usize)> {
        let slot = fv.get(feedback_idx as usize)?;

        let uninit = self.vm.specials().uninitialized_ic_sentinel.as_value();
        let mega = self.vm.specials().megamorphic_sentinel.as_value();

        // Uninitialized or megamorphic - no cache
        if slot == uninit || slot == mega {
            return None;
        }

        // SAFETY: slot is a heap object (not sentinel, not fixnum)
        let slot_handle = unsafe { slot.as_heap_handle_unchecked() };

        // Check if monomorphic (FeedbackEntry)
        if let Some(entry) = slot_handle.downcast_ref::<FeedbackEntry>() {
            // Check receiver map matches
            if entry.receiver_map != receiver_map {
                return None;
            }
            // Check holder map still valid
            let current_holder_map =
                unsafe { entry.holder.cast::<SlotObject>() }.map;
            if entry.holder_map != current_holder_map {
                return None;
            }
            return Some((entry.holder, entry.slot_index()));
        }

        // Check if polymorphic (Array of FeedbackEntry)
        if let Some(entries) = slot_handle.downcast_ref::<Array>() {
            for i in 0..entries.size() {
                let entry_val = entries.get(i)?;
                // SAFETY: polymorphic array contains FeedbackEntry objects
                let entry_handle =
                    unsafe { entry_val.as_heap_handle_unchecked() };
                let entry = entry_handle.downcast_ref::<FeedbackEntry>()?;

                if entry.receiver_map == receiver_map {
                    // Check holder map still valid
                    let current_holder_map =
                        unsafe { entry.holder.cast::<SlotObject>() }.map;
                    if entry.holder_map == current_holder_map {
                        return Some((entry.holder, entry.slot_index()));
                    }
                }
            }
        }

        None
    }

    /// Update the IC after a successful lookup.
    /// Only caches if the lookup didn't traverse an assignable parent slot.
    #[cfg(feature = "inline-cache")]
    fn update_ic(
        &mut self,
        mut fv: Handle<Array>,
        feedback_idx: u16,
        receiver_map: Handle<Map>,
        holder: Handle<HeapValue>,
        slot_index: usize,
        traversed_assignable_parent: bool,
    ) {
        // Don't cache if we went through an assignable parent
        if traversed_assignable_parent {
            return;
        }

        let holder_map = unsafe { holder.cast::<SlotObject>() }.map;

        let idx = feedback_idx as usize;
        let slot = unsafe { fv.get_unchecked(idx) };

        let uninit = self.vm.specials().uninitialized_ic_sentinel.as_value();
        let mega = self.vm.specials().megamorphic_sentinel.as_value();

        // Already megamorphic - don't update
        if slot == mega {
            return;
        }

        let fv_handle = fv.as_heap_value_handle();

        if slot == uninit {
            // Uninitialized → Monomorphic
            let entry = self.heap.allocate_feedback_entry(
                receiver_map,
                holder_map,
                holder,
                slot_index,
            );
            self.heap
                .write_barrier(fv_handle, entry.as_heap_value_handle());
            unsafe { fv.set_unchecked(idx, entry.as_value()) };
            return;
        }

        // SAFETY: not a sentinel, must be heap object
        let slot_handle = unsafe { slot.as_heap_handle_unchecked() };

        // Monomorphic → Polymorphic
        if slot_handle.downcast_ref::<FeedbackEntry>().is_some() {
            let new_entry = self.heap.allocate_feedback_entry(
                receiver_map,
                holder_map,
                holder,
                slot_index,
            );
            let entries =
                self.heap.allocate_array(&[slot, new_entry.as_value()]);
            self.heap
                .write_barrier(fv_handle, entries.as_heap_value_handle());
            unsafe { fv.set_unchecked(idx, entries.as_value()) };
            return;
        }

        // Polymorphic → add entry or megamorphic
        if let Some(entries) = slot_handle.downcast_ref::<Array>() {
            const MAX_POLYMORPHIC_ENTRIES: usize = 4;
            if entries.size() >= MAX_POLYMORPHIC_ENTRIES {
                // → Megamorphic
                unsafe { fv.set_unchecked(idx, mega) };
                return;
            }

            // Add new entry
            let new_entry = self.heap.allocate_feedback_entry(
                receiver_map,
                holder_map,
                holder,
                slot_index,
            );

            let mut new_entries_data: Vec<Value> = entries.fields().to_vec();
            new_entries_data.push(new_entry.as_value());

            let new_entries = self.heap.allocate_array(&new_entries_data);
            self.heap
                .write_barrier(fv_handle, new_entries.as_heap_value_handle());
            unsafe { fv.set_unchecked(idx, new_entries.as_value()) };
        }
    }

    /// Dispatch using cached IC data.
    #[cfg(feature = "inline-cache")]
    fn dispatch_from_ic(
        &mut self,
        receiver: Handle<Value>,
        holder: Handle<HeapValue>,
        slot_index: usize,
    ) -> ExecutionResult {
        let holder_obj = unsafe { holder.cast::<SlotObject>() };
        let slots = holder_obj.map.slots();
        debug_assert!(slot_index < slots.len(), "IC slot_index out of bounds");
        let slot = slots[slot_index];

        // Assignment slot - write to holder
        if slot.tags().contains(SlotTags::ASSIGNMENT) {
            let offset: usize =
                slot.value.as_tagged_fixnum::<usize>().unwrap().into();

            // SAFETY: stack verified by caller
            let new_value = unsafe { self.state.pop_unchecked() };

            // SAFETY: holder is valid SlotObject
            let mut holder_mut = holder_obj;
            if new_value.is_object() {
                let val_obj = unsafe { new_value.as_heap_handle_unchecked() };
                self.heap
                    .write_barrier(holder_mut.as_heap_value_handle(), val_obj);
            }
            unsafe { holder_mut.set_slot_unchecked(offset, new_value) };
            return ExecutionResult::Normal;
        }

        // Assignable slot (getter) - read from holder's assignable slots
        if slot.tags().contains(SlotTags::ASSIGNABLE) {
            let offset: usize =
                slot.value.as_tagged_fixnum::<usize>().unwrap().into();

            // SAFETY: offset is valid by construction
            let value = unsafe { holder_obj.get_slot_unchecked(offset) };
            self.state.push(value);
            return ExecutionResult::Normal;
        }

        // Primitive
        if slot.tags().contains(SlotTags::PRIMITIVE) {
            let id: usize =
                slot.value.as_tagged_fixnum::<usize>().unwrap().into();
            let message_idx = unsafe { PrimitiveMessageIndex::from_usize(id) };
            return self.primitive_send(receiver, message_idx);
        }

        // Fixnum value - push directly
        if slot.value.is_fixnum() {
            self.state.push(slot.value);
            return ExecutionResult::Normal;
        }

        // SAFETY: must be heap object
        let heap_val = unsafe { slot.value.as_heap_handle_unchecked() };

        // Method (SlotObject with code)
        if let Some(obj) = heap_val.downcast_ref::<SlotObject>()
            && obj.map.has_code()
        {
            let method = unsafe {
                slot.value.as_handle_unchecked().cast::<SlotObject>()
            };

            if let Err(e) = self.add_method(receiver, method) {
                return e;
            }

            return ExecutionResult::ActivationChanged;
        }

        // Constant value - push
        self.state.push(slot.value);
        ExecutionResult::Normal
    }

    /// Dispatch based on a SlotDescriptor (used for IC miss path).
    fn dispatch_slot(
        &mut self,
        receiver: Handle<Value>,
        slot: crate::SlotDescriptor,
    ) -> ExecutionResult {
        // Assignment slot
        if slot.tags().contains(SlotTags::ASSIGNMENT) {
            let offset: usize =
                slot.value.as_tagged_fixnum::<usize>().unwrap().into();

            // SAFETY: must be valid by protocol
            let new_value = unsafe { self.state.pop_unchecked() };

            let recv_val = receiver.inner();
            // SAFETY: must be valid by protocol
            let mut recv_obj = unsafe {
                recv_val.as_heap_handle_unchecked().cast::<SlotObject>()
            };
            if new_value.is_object() {
                // SAFETY: must be valid by protocol
                let val_obj = unsafe { new_value.as_heap_handle_unchecked() };
                self.heap
                    .write_barrier(recv_obj.as_heap_value_handle(), val_obj);
            }
            // SAFETY: offset has been bounds-checked by lookup above.
            unsafe { recv_obj.set_slot_unchecked(offset, new_value) };
            return ExecutionResult::Normal;
        }

        // Primitive
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

        // Fixnum value
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

    /// Executes bytecode until all activations complete.
    pub fn execute(&mut self) -> ExecutionResult {
        // Run until depth < 1 (aka 0)
        self.execute_until_depth(1)
    }

    /// Executes only the current activation without entering callees.
    pub fn execute_current_activation(&mut self) -> ExecutionResult {
        let depth = self.activations.depth();
        self.execute_until_depth(depth)
    }

    /// Executes bytecode until the activation stack depth reaches `target_depth`.
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
            let opcode = {
                // SAFETY: context is initializd
                let ctx = unsafe { self.context_unchecked_mut() };
                ctx.fetch_opcode()
            };
            // SAFETY: context just initalized
            let res = unsafe { self.execute_bytecode(opcode) };

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
    pub unsafe fn execute_bytecode(&mut self, op: OpCode) -> ExecutionResult {
        // --- FAST PATHS ---
        match op {
            OpCode::PushConstant => {
                // SAFETY: setup correctly by compiler
                let ctx = unsafe { self.context_unchecked_mut() };
                let idx = ctx.read_u16();
                let val = ctx.fetch_constant(idx);
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
                // SAFETY: context initialized by caller
                let ctx = unsafe { self.context_unchecked_mut() };
                let val = ctx.read_i32();
                self.state.push((val as i64).into());
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
            _ => unsafe { self.execute_bytecode_slow(op) },
        }
    }

    /// # Safety
    /// context must be correctly initialized before
    #[inline(never)]
    unsafe fn execute_bytecode_slow(&mut self, op: OpCode) -> ExecutionResult {
        // SAFETY: caller guarantees context is correctly initialized
        unsafe {
            match op {
                OpCode::Send => {
                    // Read operands
                    let selector_idx = self.context_unchecked_mut().read_u16();
                    #[cfg(feature = "inline-cache")]
                    let feedback_idx = self.context_unchecked_mut().read_u16();
                    #[cfg(not(feature = "inline-cache"))]
                    let _ = self.context_unchecked_mut().read_u16(); // skip feedback_idx

                    // Now sync context so GC sees correct IP (after operands)
                    self.sync_context();

                    // SAFETY: correctly setup by compiler
                    let message_val =
                        self.context_unchecked().fetch_constant(selector_idx);
                    // SAFETY: correctly setup by compiler
                    let message =
                        message_val.as_handle_unchecked().cast::<Message>();
                    let selector =
                        Selector::new_message(message, self.vm.shared.clone());

                    self.heap.safepoint();
                    self.reload_context();

                    if let Err(e) = self.check_min_stack(1) {
                        return e;
                    }
                    // SAFETY: correctly setup by compiler
                    let found_receiver =
                        self.state.pop_unchecked().as_handle_unchecked();

                    // Get activation's map and code for IC
                    let activation = self.activations.current().unwrap();
                    let mut act_map = activation.object.map;

                    // Increment hotness for JIT heuristics
                    act_map.increment_hotness();

                    // Try IC lookup
                    #[cfg(feature = "inline-cache")]
                    {
                        let code = act_map.code;
                        if let Some(receiver_map) =
                            self.get_receiver_map(found_receiver.inner())
                        {
                            if let Some(fv) =
                                self.ensure_feedback_vector(act_map, code)
                            {
                                if let Some((holder, slot_index)) = self
                                    .try_ic_lookup(
                                        &fv,
                                        feedback_idx,
                                        receiver_map,
                                    )
                                {
                                    // IC HIT
                                    let res = self.dispatch_from_ic(
                                        found_receiver,
                                        holder,
                                        slot_index,
                                    );
                                    self.record_depth();
                                    return res;
                                }
                            }
                        }
                    }

                    // IC MISS - full lookup
                    let res =
                        selector.clone().lookup_object(&found_receiver.inner());

                    #[cfg(feature = "inline-cache")]
                    let (slot, object, slot_index, traversed_assignable_parent) =
                        match res {
                            LookupResult::Found {
                                slot,
                                object,
                                slot_index,
                                traversed_assignable_parent,
                            } => (
                                slot,
                                object,
                                slot_index,
                                traversed_assignable_parent,
                            ),
                            LookupResult::None => {
                                let selector_name = selector
                                    .name
                                    .as_utf8()
                                    .expect("Selector must be string");
                                return ExecutionResult::Panic(format!(
                                    "Message not understood: '{}'",
                                    selector_name
                                ));
                            }
                        };

                    #[cfg(not(feature = "inline-cache"))]
                    let slot = match res {
                        LookupResult::Found { slot, .. } => slot,
                        LookupResult::None => {
                            let selector_name = selector
                                .name
                                .as_utf8()
                                .expect("Selector must be string");
                            return ExecutionResult::Panic(format!(
                                "Message not understood: '{}'",
                                selector_name
                            ));
                        }
                    };

                    // Update IC if we have feedback vector
                    #[cfg(feature = "inline-cache")]
                    {
                        let code = act_map.code;
                        if let Some(receiver_map) =
                            self.get_receiver_map(found_receiver.inner())
                        {
                            if let Some(fv) =
                                self.ensure_feedback_vector(act_map, code)
                            {
                                let holder = object
                                    .as_value()
                                    .as_heap_handle_unchecked();
                                self.update_ic(
                                    fv,
                                    feedback_idx,
                                    receiver_map,
                                    holder,
                                    slot_index,
                                    traversed_assignable_parent,
                                );
                            }
                        }
                    }

                    // Dispatch based on slot type
                    let res = self.dispatch_slot(found_receiver, slot);
                    self.record_depth();
                    res
                }
                OpCode::SendPrimitive => {
                    let prim_idx = self.context_unchecked_mut().read_u16();
                    self.sync_context();

                    // SAFETY: correctly setup by compiler
                    let prim_id =
                        PrimitiveMessageIndex::from_usize(prim_idx as usize);
                    self.heap.safepoint();
                    self.reload_context();

                    if let Err(e) = self.check_min_stack(1) {
                        return e;
                    }

                    // SAFETY: correctly setup by compiler
                    let receiver =
                        self.state.pop_unchecked().as_handle_unchecked();
                    let res = self.primitive_send(receiver, prim_id);
                    self.record_depth();
                    res
                }
                OpCode::CreateSlotObject => {
                    let map_idx = self.context_unchecked_mut().read_u16();
                    self.sync_context();

                    self.heap.safepoint();
                    self.reload_context();

                    // SAFETY: correctly setup by compiler
                    let map_val =
                        self.context_unchecked().fetch_constant(map_idx);
                    // SAFETY: correctly setup by compiler
                    let mut map = map_val.as_handle_unchecked().cast::<Map>();

                    let slot_count = map.data_slots();

                    if let Err(e) = self.check_min_stack(slot_count) {
                        return e;
                    }

                    // SAFETY: correctly setup by compiler
                    let slots =
                        self.state.stack_pop_slice_unchecked(slot_count);
                    let slots = map.collect_values(slots);

                    let obj = self.heap.allocate_slots(map, &slots);
                    self.state.push(obj.into());

                    ExecutionResult::ActivationChanged
                }
                OpCode::CreateQuotation => {
                    let map_idx = self.context_unchecked_mut().read_u16();
                    self.sync_context();

                    self.heap.safepoint();
                    self.reload_context();

                    // SAFETY: correctly setup by runtime
                    let ctx = self.context_unchecked();

                    let map_val = ctx.fetch_constant(map_idx);
                    // SAFETY: correctly setup by compiler
                    let map = map_val.as_handle_unchecked().cast::<Map>();

                    let activation = ctx.activation;

                    let quotation =
                        self.heap.allocate_quotation(map, activation);
                    self.state.push(quotation.into());

                    ExecutionResult::Normal
                }
                OpCode::Return => {
                    // Return has no operands
                    // No need to sync context as we are popping the frame
                    let _ = self.activations.pop();
                    ExecutionResult::ActivationChanged
                }
                OpCode::SendSuper => {
                    let _selector_idx = self.context_unchecked_mut().read_u16();
                    let _feedback_idx = self.context_unchecked_mut().read_u16();
                    self.sync_context();
                    unimplemented!("SendSuper")
                }
                OpCode::SendParent => {
                    let _parent_idx = self.context_unchecked_mut().read_u16();
                    let _selector_idx = self.context_unchecked_mut().read_u16();
                    let _feedback_idx = self.context_unchecked_mut().read_u16();
                    self.sync_context();
                    unimplemented!("SendParent")
                }
                // SAFETY: we match others before already
                _ => {
                    debug_assert!(
                        false,
                        "unknown opcode in execute_bytecode_slow"
                    );
                    std::hint::unreachable_unchecked()
                }
            }
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

        // SAFETY: stack depth verified above
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
            ExecutionResult::ActivationChanged => outputs
                .into_iter()
                .for_each(|out| self.state.push(out.into())),
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
        selector: &Selector,
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
            // SAFETY: offset has been bounds-checked by lookup above.
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

pub fn execute_source_with_receiver(
    interpreter: &mut Interpreter,
    source: &str,
    receiver: Handle<Value>,
) -> Result<(), String> {
    let parser = interpreter
        .heap
        .allocate_parser(&interpreter.vm.shared.strings, source.as_bytes());

    let parse_msg = interpreter
        .vm
        .intern_string_message("parse", &mut interpreter.heap);

    let constants = vec![parser.as_value(), parse_msg.as_value()];

    let mut writer = BytecodeWriter::new();
    writer.emit_push_constant(0);
    writer.emit_send(1, 0);
    writer.emit_return();

    let dummy_body = interpreter.heap.allocate_array(&[]);

    let boot_code = interpreter.heap.allocate_code(
        &constants,
        &writer.into_inner(),
        1,
        dummy_body,
        unsafe { Handle::null() },
    );

    let boot_map = interpreter.heap.allocate_executable_map(boot_code, 0, 0);

    let boot_quotation = interpreter
        .heap
        .allocate_quotation(boot_map, unsafe { Handle::null() });

    interpreter.add_quotation_with_receiver(boot_quotation, receiver);

    match interpreter.execute() {
        ExecutionResult::Normal => {}
        ExecutionResult::Panic(msg) => {
            return Err(format!("Parser Panic: {}", msg));
        }
        res => return Err(format!("Parser abnormal exit: {:?}", res)),
    }

    let body_val = match interpreter.state.pop() {
        Some(v) => v,
        None => {
            return Err("Parser did not return a value (Empty Stack)".into());
        }
    };

    if body_val == interpreter.vm.shared.specials.false_object.as_value() {
        return Err("Parsing failed (Syntax Error)".into());
    }

    let body_array = unsafe { body_val.as_handle_unchecked().cast::<Array>() };

    let code = BytecodeCompiler::compile(
        &interpreter.vm.shared,
        &mut interpreter.heap,
        body_array,
    );

    let code_map = interpreter.heap.allocate_executable_map(code, 0, 0);

    let quotation = interpreter
        .heap
        .allocate_quotation(code_map, unsafe { Handle::null() });

    interpreter.add_quotation_with_receiver(quotation, receiver);

    match interpreter.execute() {
        ExecutionResult::Normal => Ok(()),
        ExecutionResult::Panic(msg) => Err(format!("Panic: {}", msg)),
        res => Err(format!("Abnormal exit: {:?}", res)),
    }
}

impl ExecutionContext {
    #[inline(always)]
    fn debug_assert_context_layout(&self) {
        debug_assert!(!self.inst_base.is_null(), "inst_base must be non-null");
        debug_assert!(!self.ip.is_null(), "ip must be non-null");

        let code = self.activation.code();
        let inst_size = code.inst_size as usize;
        if inst_size > 0 {
            debug_assert_eq!(
                self.inst_base,
                code.instructions().as_ptr(),
                "inst_base mismatch with code.instructions()"
            );
        }

        if code.const_count > 0 {
            debug_assert_eq!(
                self.cp,
                code.constants().as_ptr(),
                "cp mismatch with code.constants()"
            );
        }
    }

    #[inline(always)]
    fn debug_assert_ip_in_bounds(&self, bytes: usize) {
        self.debug_assert_context_layout();

        let code = self.activation.code();
        let inst_size = code.inst_size as usize;
        let base = self.inst_base as usize;
        let ip = self.ip as usize;
        let end = base.saturating_add(inst_size);

        debug_assert!(
            ip >= base,
            "ip before inst_base: ip {:#x} base {:#x}",
            ip,
            base
        );
        debug_assert!(
            ip.saturating_add(bytes) <= end,
            "ip out of bounds: ip {:#x} + {} > end {:#x}",
            ip,
            bytes,
            end
        );
    }

    /// Reads the instruction at the current IP and advances the IP.
    #[inline(always)]
    pub fn fetch_opcode(&mut self) -> OpCode {
        self.debug_assert_ip_in_bounds(1);
        // SAFETY: execution context is initialized
        unsafe {
            let inst = *self.ip;
            self.ip = self.ip.add(1);
            OpCode::from_u8(inst)
        }
    }

    /// Read u8 and advance
    #[inline(always)]
    pub fn read_u8(&mut self) -> u8 {
        self.debug_assert_ip_in_bounds(1);
        // SAFETY: ip is valid within bytecode bounds
        unsafe {
            let val = *self.ip;
            self.ip = self.ip.add(1);
            val
        }
    }

    /// Read u16 and advance
    #[inline(always)]
    pub fn read_u16(&mut self) -> u16 {
        self.debug_assert_ip_in_bounds(2);
        // SAFETY: ip is valid, read_unaligned handles alignment
        unsafe {
            let ptr = self.ip as *const u16;
            let val = ptr.read_unaligned();
            self.ip = self.ip.add(2);
            val
        }
    }

    /// Read i32 and advance
    #[inline(always)]
    pub fn read_i32(&mut self) -> i32 {
        self.debug_assert_ip_in_bounds(4);
        // SAFETY: ip is valid, read_unaligned handles alignment
        unsafe {
            let ptr = self.ip as *const i32;
            let val = ptr.read_unaligned();
            self.ip = self.ip.add(4);
            val
        }
    }

    /// Fetches a value from the constant pool.
    #[inline(always)]
    pub fn fetch_constant(&self, index: u16) -> Value {
        let code = self.activation.code();
        debug_assert!(
            (index as u32) < code.const_count,
            "constant index out of bounds: {} >= {}",
            index,
            code.const_count
        );
        // SAFETY: execution context is initialized
        unsafe { *self.cp.add(index as usize) }
    }
}
