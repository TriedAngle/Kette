use crate::{ExecutionResult, ExecutionState, Executor, Handle, VMProxy, VMThreadProxy, Value};

mod bytearray;
mod fixnum;
mod stack;

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
    pub message_receiver: Handle<Value>,
    pub receiver: Handle<Value>,
    pub arguments: &'arg [Handle<Value>],
    pub result: &'arg mut [Handle<Value>],
}

impl<'ex, 'arg> PrimitiveContext<'ex, 'arg> {
    pub fn new(
        executor: &'ex mut Executor,
        receiver: Handle<Value>,
        message_receiver: Handle<Value>,
        arguments: &'arg [Handle<Value>],
        result: &'arg mut [Handle<Value>],
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
    PrimitiveMessage::new("fixnum?", 0, 1, fixnum::is_fixnum),
    PrimitiveMessage::new("2fixnum?", 1, 1, fixnum::is_2fixnum),
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
    PrimitiveMessage::new("dup", 1, 2, stack::dup),
    PrimitiveMessage::new("drop", 1, 0, stack::drop),
    PrimitiveMessage::new("2drop", 2, 0, stack::drop2),
    PrimitiveMessage::new("3drop", 3, 0, stack::drop3),
    PrimitiveMessage::new("swap", 2, 2, stack::swap),
    PrimitiveMessage::new("over", 2, 3, stack::over),
    PrimitiveMessage::new("rot", 3, 3, stack::rot),
    PrimitiveMessage::new("-rot", 3, 3, stack::neg_rot),
    PrimitiveMessage::new("spin", 3, 3, stack::spin),
    PrimitiveMessage::new("dupd", 3, 3, stack::dupd),
    PrimitiveMessage::new("dropd", 2, 2, stack::dropd),
    PrimitiveMessage::new("2dropd", 3, 3, stack::dropd2),
    PrimitiveMessage::new("swapd", 3, 3, stack::swapd),
    PrimitiveMessage::new("dip", 2, 1, stack::dip),
];

pub fn get_primitive(id: PrimitiveMessageIndex) -> PrimitiveMessage<'static> {
    debug_assert!(id.0 < PRIMITIVES.len());
    PRIMITIVES[id.0]
}
