use crate::{
    Activation, ActivationStack, ActivationType, ExecutionState, Handle,
    HeapProxy, Instruction, LookupResult, Method, PrimitiveMessageIndex,
    Quotation, Selector, SlotTags, ThreadProxy, VMProxy, Value, get_primitive,
    transmute,
};

pub struct Interpreter {
    pub vm: VMProxy,
    pub thread: ThreadProxy,
    pub heap: HeapProxy,
    pub state: ExecutionState,
    pub activations: ActivationStack,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum IntegerError {
    Overflow,
    DivisionByZero,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum ExecutionResult {
    Normal,
    IntegerError(IntegerError),
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
        }
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
            let instructions = unsafe { &(*code).instructions };
            return Some(instructions[index]);
        }
        None
    }

    pub fn setup(&mut self, quotation: Handle<Quotation>) {
        let new = self.heap.allocate_quotation_activation(quotation, &[]);
        self.activations
            .new_activation(new, ActivationType::Quotation);
    }

    pub fn execute(&mut self) -> ExecutionResult {
        while let Some(instruction) = self.current_instruction() {
            let res = self.execute_single_bytecode(instruction);
            match res {
                ExecutionResult::Normal => (),
                _ => unimplemented!("TODO"),
            }
            self.increment_instruction();
        }

        ExecutionResult::Normal
    }

    pub fn execute_single_bytecode(
        &mut self,
        instruction: Instruction,
    ) -> ExecutionResult {
        match instruction {
            Instruction::PushFixnum { value } => {
                tracing::trace!("push_fixnum: {:?}", value);
                self.state.push(value.into());
                self.record_depth();
                ExecutionResult::Normal
            }
            Instruction::PushValue { value } => {
                tracing::trace!("push_value: {:?}", value);
                self.state.push(value);
                self.record_depth();
                ExecutionResult::Normal
            }
            Instruction::AllocateSlotObject { map } => {
                tracing::trace!("allocate_slot_object: {:?}", map);
                // SAFETY: map must be valid here
                let map_ref = unsafe { map.as_ref() };
                let slot_count = map_ref.assignable_slots_count();
                // SAFETY: not safe yet, TODO: depth check
                let slots =
                    unsafe { self.state.stack_pop_slice_unchecked(slot_count) };
                let obj = self.heap.allocate_slot_object(map, slots);
                self.state.push(obj.into());
                self.record_depth();
                ExecutionResult::Normal
            }
            Instruction::SendPrimitive { id } => {
                // SAFETY: after depth check, this is safe
                let receiver =
                    unsafe { self.state.pop_unchecked().as_handle_unchecked() };
                let res = self.primitive_send(receiver, id);
                self.record_depth();
                res
            }
            Instruction::Send { message } => {
                let selector =
                    Selector::new_message(message, self.vm.shared.clone());

                // SAFETY: after depth check, this is safe
                let receiver =
                    unsafe { self.state.pop_unchecked().as_handle_unchecked() };
                let res = self.send(receiver, selector);
                self.record_depth();
                res
            }
            Instruction::SendNamed { message } => {
                let message = self.vm.intern_string(message, &mut self.heap);
                let selector = Selector::new(message, self.vm.shared.clone());
                // SAFETY: after depth check, this is safe
                let receiver =
                    unsafe { self.state.pop_unchecked().as_handle_unchecked() };
                let res = self.send(receiver, selector);
                self.record_depth();
                res
            }
            Instruction::Return => {
                tracing::trace!(target: "interpreter", "callstack depth {}", self.activations.depth());
                let _last = self.activations.pop();
                ExecutionResult::Normal
            }
            _ => unimplemented!("TODO: implement"),
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

        let res = selector.lookup_object(&receiver.inner());

        let slot = match res {
            LookupResult::Found { slot, .. } => slot,
            LookupResult::None => {
                panic!("TODO: implement error handling")
            }
        };

        if slot
            .tags()
            .contains(SlotTags::EXECUTABLE | SlotTags::PRIMITIVE)
        {
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

        if slot.tags().contains(!SlotTags::EXECUTABLE) {
            self.state.push(slot.value);
            return ExecutionResult::Normal;
        }

        // SAFETY: must by protocol
        let method =
            unsafe { slot.value.as_handle_unchecked().cast::<Method>() };
        // SAFETY: safe by protocol
        let map = unsafe { method.map.promote_to_handle() };

        let slot_count = map.slot_count();

        // idea: peek here, this saves the inputs,
        // now just continue with normal stack
        // TODO: we should probably also store depth?
        // could be important to reset state
        // SAFETY: TODO: depth check
        let slots =
            unsafe { self.state.stack_peek_slice_unchecked(slot_count) };
        // SAFETY: TODO: actually put them into handle set
        let slots = unsafe { crate::transmute::values_as_handles(slots) };

        let activation_object =
            self.heap.allocate_method_activation(receiver, map, slots);

        self.activations
            .new_activation(activation_object, ActivationType::Method);

        // SAFETY: not safe yet, TOOD: depth check
        // let inputs = unsafe { self.state.stack_pop_unchecked(message.inputs) };
        // the initialization is guaranted after the call
        // let mut outputs = Vec::with_capacity(message.outputs);

        // SAFETY: gc not running
        // let inputs = unsafe { transmute::values_as_handles(inputs.as_slice()) };
        unimplemented!()
    }
}
