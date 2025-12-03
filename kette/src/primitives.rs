use crate::{
    ExecutionResult, ExecutionState, Handle, HeapProxy, Interpreter, Parser, ParserRegistry,
    ThreadProxy, VMProxy, Value,
};

mod bytearray;
mod fixnum;
mod parsing;
mod stack;
mod threads;

#[repr(transparent)]
#[derive(Debug, Copy, Clone)]
pub struct PrimitiveMessageIndex(usize);

#[repr(transparent)]
#[derive(Debug, Copy, Clone)]
pub struct PrimitiveParserIndex(usize);

pub type PrimitiveFunction = fn(&mut PrimitiveContext) -> ExecutionResult;
pub type PrimitiveParserFunction = fn(&mut PrimitiveParserContext) -> ExecutionResult;

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

#[derive(Debug, Copy, Clone)]
pub struct PrimitiveParser<'a> {
    pub name: &'a str,
    pub ptr: PrimitiveParserFunction,
}

impl<'a> PrimitiveParser<'a> {
    pub const fn new(name: &'a str, ptr: PrimitiveParserFunction) -> Self {
        Self { name, ptr }
    }
}

pub struct PrimitiveContext<'ex, 'arg> {
    pub state: &'ex mut ExecutionState,
    pub vm: &'ex VMProxy,
    pub thread: &'ex ThreadProxy,
    pub heap: &'ex mut HeapProxy,
    pub receiver: Handle<Value>,
    pub arguments: &'arg [Handle<Value>],
    pub result: &'arg mut [Handle<Value>],
}

impl<'ex, 'arg> PrimitiveContext<'ex, 'arg> {
    pub fn new(
        interpreter: &'ex mut Interpreter,
        receiver: Handle<Value>,
        arguments: &'arg [Handle<Value>],
        result: &'arg mut [Handle<Value>],
    ) -> Self {
        let state = &mut interpreter.state;
        let vm = &interpreter.vm;
        let thread = &interpreter.thread;
        let heap = &mut interpreter.heap;
        Self {
            state,
            vm,
            thread,
            heap,
            receiver,
            arguments,
            result,
        }
    }

    pub fn call<'m>(
        message: &'m PrimitiveMessage,
        interpreter: &'ex mut Interpreter,
        receiver: Handle<Value>,
        arguments: &'arg [Handle<Value>],
        result: &'arg mut [Handle<Value>],
    ) -> ExecutionResult {
        let mut ctx = Self::new(interpreter, receiver, arguments, result);

        (message.ptr)(&mut ctx)
    }
}

impl<'m> PrimitiveMessage<'m> {
    pub fn call<'ex, 'arg>(
        &'m self,
        interpreter: &'ex mut Interpreter,
        receiver: Handle<Value>,
        arguments: &'arg [Handle<Value>],
        result: &'arg mut [Handle<Value>],
    ) -> ExecutionResult {
        let mut ctx = PrimitiveContext::new(interpreter, receiver, arguments, result);

        (self.ptr)(&mut ctx)
    }
}

pub struct PrimitiveParserContext<'ex, 'code> {
    pub state: &'ex mut ExecutionState,
    pub vm: &'ex VMProxy,
    pub thread: &'ex ThreadProxy,
    pub heap: &'ex mut HeapProxy,
    pub parser: &'ex mut Parser<'code>,
    pub parsers: &'ex ParserRegistry,
}

impl<'ex, 'code> PrimitiveParserContext<'ex, 'code> {
    pub fn new(
        interpreter: &'ex mut Interpreter,
        parser: &'ex mut Parser<'code>,
        parsers: &'ex ParserRegistry,
    ) -> Self {
        let state = &mut interpreter.state;
        let thread = &interpreter.thread;
        let heap = &mut interpreter.heap;
        let vm = &interpreter.vm;
        Self {
            state,
            vm,
            thread,
            heap,
            parser,
            parsers,
        }
    }
}

pub const PRIMITIVES: &[PrimitiveMessage] = &[
    // Stack
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
    // Fixnum
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
    // Bytearrays
    PrimitiveMessage::new("fixnum>utf8-bytes", 0, 1, bytearray::fixnum_to_utf8_bytes),
    PrimitiveMessage::new("bytearray-print", 0, 0, bytearray::bytearray_print),
    PrimitiveMessage::new("bytearray-println", 0, 0, bytearray::bytearray_println),
    // Threads
    PrimitiveMessage::new("<thread-native>", 0, 0, threads::create_native),
    PrimitiveMessage::new("thread-join", 0, 0, threads::join),
    PrimitiveMessage::new("thread-join-timeout", 1, 0, threads::join_timeout),
    PrimitiveMessage::new("park", 1, 0, threads::park),
    PrimitiveMessage::new("park-nanos", 2, 0, threads::park_nanos),
    PrimitiveMessage::new("park-until", 2, 0, threads::park_until),
    PrimitiveMessage::new("unpark", 0, 0, threads::unpark),
];

// TODO: merge this
pub const PRIMITIVE_PARSERS: &[PrimitiveParser] = &[];

pub fn get_primitive(id: PrimitiveMessageIndex) -> PrimitiveMessage<'static> {
    debug_assert!(id.0 < PRIMITIVES.len());
    PRIMITIVES[id.0]
}

pub fn primitive_index(name: &str) -> PrimitiveMessageIndex {
    PRIMITIVES
        .iter()
        .position(|prim| prim.name == name)
        .map(PrimitiveMessageIndex)
        .expect("Primitive Exists")
}
