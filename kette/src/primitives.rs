use crate::{ExecutionResult, ExecutionState, Executor, TaggedValue, VMProxy, VMThreadProxy};

mod bytearray;
mod fixnum;

#[repr(transparent)]
#[derive(Debug, Copy, Clone)]
pub struct PrimitiveMessageIndex(usize);

pub type PrimitiveFunction = fn(&mut PrimitiveContext) -> ExecutionResult;

// self does not count as input
// e.g. `+` => `3 5 +` has inputs: 1
#[derive(Debug, Copy, Clone)]
pub struct PrimitiveMessage<'a> {
    pub name: &'a str,
    pub inputs: usize,
    pub outputs: usize,
    pub ptr: PrimitiveFunction,
}

impl<'a> PrimitiveMessage<'a> {
    pub const fn new(name: &'a str, inputs: usize, outputs: usize, ptr: PrimitiveFunction) -> Self {
        Self {
            name,
            inputs,
            outputs,
            ptr,
        }
    }
}

pub struct PrimitiveContext<'ex, 'arg> {
    pub state: &'ex mut ExecutionState,
    pub thread: &'ex VMThreadProxy,
    pub vm: &'ex VMProxy,
    // in normal calls receiver message receiver are the same
    // but if with super, or delegate they may differ
    pub message_receiver: TaggedValue,
    pub receiver: TaggedValue,
    pub arguments: &'arg [TaggedValue],
    pub result: &'arg mut [TaggedValue],
}

impl<'ex, 'arg> PrimitiveContext<'ex, 'arg> {
    pub fn new(
        executor: &'ex mut Executor,
        receiver: TaggedValue,
        message_receiver: TaggedValue,
        arguments: &'arg [TaggedValue],
        result: &'arg mut [TaggedValue],
    ) -> Self {
        let state = &mut executor.state;
        let thread = &executor.thread;
        let vm = &thread.vm;
        Self {
            state,
            thread,
            vm,
            message_receiver,
            receiver,
            arguments,
            result,
        }
    }
}

pub const PRIMITIVES: &[PrimitiveMessage] = &[
    PrimitiveMessage::new("fixnum+", 1, 1, fixnum::fixnum_add),
    PrimitiveMessage::new("fixnum-", 1, 1, fixnum::fixnum_sub),
    PrimitiveMessage::new("fixnum*", 1, 1, fixnum::fixnum_mul),
    PrimitiveMessage::new("fixnum/", 1, 1, fixnum::fixnum_div),
    PrimitiveMessage::new("fixnum%", 1, 1, fixnum::fixnum_mod),
    PrimitiveMessage::new("fixnum-neg", 1, 1, fixnum::fixnum_neg),
    PrimitiveMessage::new("fixnum-and", 1, 1, fixnum::fixnum_and),
    PrimitiveMessage::new("fixnum-or", 1, 1, fixnum::fixnum_or),
    PrimitiveMessage::new("fixnum-eq", 1, 1, fixnum::fixnum_eq),
    PrimitiveMessage::new("fixnum-neq", 1, 1, fixnum::fixnum_neq),
    PrimitiveMessage::new("fixnum-lt", 1, 1, fixnum::fixnum_lt),
    PrimitiveMessage::new("fixnum-gt", 1, 1, fixnum::fixnum_gt),
    PrimitiveMessage::new("fixnum-leq", 1, 1, fixnum::fixnum_leq),
    PrimitiveMessage::new("fixnum-geq", 1, 1, fixnum::fixnum_geq),
    PrimitiveMessage::new("fixnum>utf8-bytes", 0, 1, bytearray::fixnum_to_utf8_bytes),
    PrimitiveMessage::new("bytearray-print", 0, 0, bytearray::bytearray_print),
    PrimitiveMessage::new("bytearray-println", 0, 0, bytearray::bytearray_println),
];

pub fn get_primitive(id: PrimitiveMessageIndex) -> PrimitiveMessage<'static> {
    debug_assert!(id.0 < PRIMITIVES.len());
    PRIMITIVES[id.0]
}
