use std::mem;

use crate::{
    ExecutionResult, ExecutionState, Handle, HeapProxy, Interpreter,
    ThreadProxy, VMProxy, Value,
};

mod array;
mod bignum;
mod bytearray;
mod fixnum;
mod float;
mod general;
mod message;
mod method;
mod parsing;
mod quotation;
mod error;
mod stack;
mod threads;
mod vector;
pub use vector::Vector;

#[repr(transparent)]
#[derive(Debug, Copy, Clone)]
pub struct PrimitiveMessageIndex(usize);

impl PrimitiveMessageIndex {
    /// # Safety
    /// id must be a valid primitive id
    pub unsafe fn from_usize(id: usize) -> Self {
        Self(id)
    }

    pub fn as_raw(self) -> usize {
        self.0
    }
}

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
    pub const fn new(
        name: &'a str,
        inputs: usize,
        outputs: usize,
        ptr: PrimitiveFunction,
    ) -> Self {
        Self {
            name,
            inputs,
            outputs,
            ptr,
        }
    }
}

// TODO: remove this unused
#[allow(unused)]
#[derive(Debug, Copy, Clone)]
pub struct PrimitiveParser<'a> {
    pub name: &'a str,
    pub ptr: PrimitiveFunction,
}

impl<'a> PrimitiveParser<'a> {
    // TODO: remove this unused
    #[allow(unused)]
    pub const fn new(name: &'a str, ptr: PrimitiveFunction) -> Self {
        Self { name, ptr }
    }
}

pub struct PrimitiveContext<'ex, 'arg> {
    pub interpreter: &'ex mut Interpreter,
    pub state: &'ex mut ExecutionState,
    pub vm: &'ex VMProxy,
    pub thread: &'ex ThreadProxy,
    pub heap: &'ex mut HeapProxy,
    pub receiver: Handle<Value>,
    pub inputs: &'arg [Handle<Value>],
    pub outputs: &'arg mut [Handle<Value>],
}

impl<'ex, 'arg> PrimitiveContext<'ex, 'arg> {
    pub fn new(
        interpreter: &'ex mut Interpreter,
        receiver: Handle<Value>,
        inputs: &'arg [Handle<Value>],
        outputs: &'arg mut [Handle<Value>],
    ) -> Self {
        // SAFETY: this is very dangerous, but we got motion
        let ereased = unsafe {
            mem::transmute::<&mut Interpreter, &'ex mut Interpreter>(
                interpreter,
            )
        };
        let state = &mut interpreter.state;
        let vm = &interpreter.vm;
        let thread = &interpreter.thread;
        let heap = &mut interpreter.heap;
        Self {
            interpreter: ereased,
            state,
            vm,
            thread,
            heap,
            receiver,
            inputs,
            outputs,
        }
    }

    pub fn call<'m>(
        message: &'m PrimitiveMessage,
        interpreter: &'ex mut Interpreter,
        receiver: Handle<Value>,
        inputs: &'arg [Handle<Value>],
        outputs: &'arg mut [Handle<Value>],
    ) -> ExecutionResult {
        let mut ctx = Self::new(interpreter, receiver, inputs, outputs);

        (message.ptr)(&mut ctx)
    }

    pub fn new_invoke<'arg2>(
        &mut self,
        receiver: Handle<Value>,
        inputs: &'arg2 [Handle<Value>],
        outputs: &'arg2 mut [Handle<Value>],
    ) -> PrimitiveContext<'_, 'arg2> {
        PrimitiveContext {
            interpreter: self.interpreter,
            vm: self.vm,
            heap: self.heap,
            state: self.state,
            thread: self.thread,
            receiver,
            inputs,
            outputs,
        }
    }
}

impl<'m> PrimitiveMessage<'m> {
    pub fn call<'ex, 'arg>(
        &'m self,
        interpreter: &'ex mut Interpreter,
        receiver: Handle<Value>,
        inputs: &'arg [Handle<Value>],
        outputs: &'arg mut [Handle<Value>],
    ) -> ExecutionResult {
        let mut ctx =
            PrimitiveContext::new(interpreter, receiver, inputs, outputs);

        (self.ptr)(&mut ctx)
    }

    pub fn call_with_context(
        &'m self,
        ctx: &mut PrimitiveContext,
    ) -> ExecutionResult {
        (self.ptr)(ctx)
    }
}

#[rustfmt::skip]
pub const PRIMITIVES: &[PrimitiveMessage] = &[
    // Stack
    PrimitiveMessage::new("dup", 1, 2, stack::dup),
    PrimitiveMessage::new("2dup", 2, 4, stack::dup2),
    PrimitiveMessage::new("drop", 1, 0, stack::drop),
    PrimitiveMessage::new("2drop", 2, 0, stack::drop2),
    PrimitiveMessage::new("3drop", 3, 0, stack::drop3),
    PrimitiveMessage::new("swap", 2, 2, stack::swap),
    PrimitiveMessage::new("over", 2, 3, stack::over),
    PrimitiveMessage::new("pick", 3, 4, stack::pick),
    PrimitiveMessage::new("rot", 3, 3, stack::rot),
    PrimitiveMessage::new("-rot", 3, 3, stack::neg_rot),
    PrimitiveMessage::new("spin", 3, 3, stack::spin),
    PrimitiveMessage::new("dupd", 2, 3, stack::dupd),
    PrimitiveMessage::new("dropd", 2, 1, stack::dropd),
    PrimitiveMessage::new("2dropd", 3, 1, stack::dropd2),
    PrimitiveMessage::new("swapd", 3, 3, stack::swapd),
    PrimitiveMessage::new("@vm-depth", 0, 1, stack::depth),
    // Fixnum
    PrimitiveMessage::new("fixnum?", 0, 1, fixnum::is_fixnum),
    PrimitiveMessage::new("2fixnum?", 1, 1, fixnum::is_2fixnum),
    PrimitiveMessage::new("fixnum+", 1, 1, fixnum::fixnum_add),
    PrimitiveMessage::new("fixnum-", 1, 1, fixnum::fixnum_sub),
    PrimitiveMessage::new("fixnum*", 1, 1, fixnum::fixnum_mul),
    PrimitiveMessage::new("fixnum/", 1, 1, fixnum::fixnum_div),
    PrimitiveMessage::new("fixnum%", 1, 1, fixnum::fixnum_mod),
    PrimitiveMessage::new("fixnum^", 1, 1, fixnum::fixnum_pow),
    PrimitiveMessage::new("fixnumNeg", 0, 1, fixnum::fixnum_neg),
    PrimitiveMessage::new("fixnumBitAnd", 1, 1, fixnum::fixnum_and),
    PrimitiveMessage::new("fixnumBitOr", 1, 1, fixnum::fixnum_or),
    PrimitiveMessage::new("fixnum=", 1, 1, fixnum::fixnum_eq),
    PrimitiveMessage::new("fixnum!=", 1, 1, fixnum::fixnum_neq),
    PrimitiveMessage::new("fixnum<", 1, 1, fixnum::fixnum_lt),
    PrimitiveMessage::new("fixnum>", 1, 1, fixnum::fixnum_gt),
    PrimitiveMessage::new("fixnum<=", 1, 1, fixnum::fixnum_leq),
    PrimitiveMessage::new("fixnum>=", 1, 1, fixnum::fixnum_geq),
    PrimitiveMessage::new("fixnum>string", 0, 1, fixnum::fixnum_to_utf8_bytes),
    PrimitiveMessage::new("fixnumParent", 0, 1, fixnum::parent),
    // Float 
    PrimitiveMessage::new("float?", 0, 1, float::is_float),
    PrimitiveMessage::new("2float?", 1, 1, float::is_2float),
    PrimitiveMessage::new("float+", 1, 1, float::float_add),
    PrimitiveMessage::new("float-", 1, 1, float::float_sub),
    PrimitiveMessage::new("float*", 1, 1, float::float_mul),
    PrimitiveMessage::new("float/", 1, 1, float::float_div),
    PrimitiveMessage::new("float%", 1, 1, float::float_mod),
    PrimitiveMessage::new("float^", 1, 1, float::float_pow),
    PrimitiveMessage::new("floatSqrt", 0, 1, float::float_sqrt),
    PrimitiveMessage::new("floate^", 0, 1, float::float_exp),
    PrimitiveMessage::new("float2^", 0, 1, float::float_exp2),
    PrimitiveMessage::new("floatSin", 0, 1, float::float_sin),
    PrimitiveMessage::new("floatCos", 0, 1, float::float_cos),
    PrimitiveMessage::new("floatTan", 0, 1, float::float_tan),
    PrimitiveMessage::new("floatAsin", 0, 1, float::float_asin),
    PrimitiveMessage::new("floatAcos", 0, 1, float::float_acos),
    PrimitiveMessage::new("floatAtan", 0, 1, float::float_atan),
    PrimitiveMessage::new("floatNeg", 0, 1, float::float_neg),
    PrimitiveMessage::new("float=", 1, 1, float::float_eq),
    PrimitiveMessage::new("float!=", 1, 1, float::float_neq),
    PrimitiveMessage::new("float<", 1, 1, float::float_lt),
    PrimitiveMessage::new("float>", 1, 1, float::float_gt),
    PrimitiveMessage::new("float<=", 1, 1, float::float_leq),
    PrimitiveMessage::new("float>=", 1, 1, float::float_geq),
    PrimitiveMessage::new("float>string", 0, 1, float::float_to_utf8_bytes),
    PrimitiveMessage::new("floatParent", 0, 1, float::parent),
    // Bytearrays
    PrimitiveMessage::new("(print)", 0, 0, bytearray::bytearray_print),
    PrimitiveMessage::new("(println)", 0, 0, bytearray::bytearray_println),
    PrimitiveMessage::new("bytearrayParent", 0, 1, bytearray::parent),
    PrimitiveMessage::new("(bytearraySize)",0 , 1, bytearray::size),
    PrimitiveMessage::new("(bytearrayNew)", 1, 1, bytearray::bytearray_new),
    PrimitiveMessage::new("(bytearrayAt)", 1, 1, bytearray::bytearray_at),
    PrimitiveMessage::new("(bytearrayAtPut)", 2, 0, bytearray::bytearray_at_put),
    PrimitiveMessage::new("(bytearrayMemset)", 3, 0, bytearray::bytearray_memset),
    PrimitiveMessage::new("(bytearrayMemcpy)", 4, 0, bytearray::bytearray_memcpy),
    // Arrays
    PrimitiveMessage::new("(>quotation)", 0, 1, array::array_to_quotation),
    PrimitiveMessage::new("arrayParent", 0, 1, array::parent),
    PrimitiveMessage::new("(arraySize)",0 , 1, array::size),
    PrimitiveMessage::new("(arrayNew)", 2, 1, array::array_new),
    PrimitiveMessage::new("(arrayAt)", 1, 1, array::array_at),
    PrimitiveMessage::new("(arrayAtPut)", 2, 0, array::array_at_put),
    // Quotation
    PrimitiveMessage::new("(call)", 0, 0, quotation::call),
    PrimitiveMessage::new("dip", 1, 1, quotation::dip),
    PrimitiveMessage::new("if", 2, 0, quotation::conditional_branch),
    PrimitiveMessage::new("quotationParent", 0, 1, quotation::parent),
    // Threads
    PrimitiveMessage::new("<threadNative>", 0, 0, threads::create_native),
    PrimitiveMessage::new("threadJoin", 0, 0, threads::join),
    PrimitiveMessage::new("threadJoinTimeout", 1, 0, threads::join_timeout),
    PrimitiveMessage::new("park", 1, 0, threads::park),
    PrimitiveMessage::new("parkNanos", 2, 0, threads::park_nanos),
    PrimitiveMessage::new("parkUntil", 2, 0, threads::park_until),
    PrimitiveMessage::new("unpark", 0, 0, threads::unpark),
    // parsing
    PrimitiveMessage::new("parseNext", 0, 1, parsing::parse_next),
    PrimitiveMessage::new("parseUntil", 1, 1, parsing::parse_until),
    PrimitiveMessage::new("parse", 0, 1, parsing::parse_complete),
    PrimitiveMessage::new("messageParent", 0, 1, message::parent),
    PrimitiveMessage::new("messageName", 0, 1, message::name),
    // Parse Time
    PrimitiveMessage::new("[", 1, 1, parsing::parse_quotation),
    PrimitiveMessage::new("(|", 1, 1, parsing::parse_object),
    PrimitiveMessage::new("//", 1, 1, parsing::parse_line_comment),
    PrimitiveMessage::new("/*", 1, 1, parsing::parse_block_comment),
    PrimitiveMessage::new("$[", 1, 1, parsing::parse_execute),
    // Method
    // PrimitiveMessage::new("(call-method)", 1, 0, method::call),
    // Primitive Vector
    PrimitiveMessage::new("vectorPush", 1, 0, vector::push),
    // General
    PrimitiveMessage::new("addTraitSlots", 2, 0, general::add_trait_slots),
    PrimitiveMessage::new("removeTraitSlots", 2, 0, general::remove_trait_slots),
    PrimitiveMessage::new("(identity)", 0, 1, general::identity),
    PrimitiveMessage::new("(clone)", 1, 1, general::clone_obj),
    PrimitiveMessage::new("(cloneBoa)", 1, 1, general::clone_obj_boa),
    // errors
    PrimitiveMessage::new("(signal)", 1, 0,error::signal),
    PrimitiveMessage::new("(withHandler)", 2, 0,error::with_handler),
    PrimitiveMessage::new("(unwind)", 1, 0,error::unwind),
];

pub fn get_primitive(id: PrimitiveMessageIndex) -> PrimitiveMessage<'static> {
    debug_assert!(id.0 < PRIMITIVES.len());
    PRIMITIVES[id.0]
}

pub fn primitive_index(name: &str) -> PrimitiveMessageIndex {
    PRIMITIVES
        .iter()
        .position(|prim| prim.name == name)
        .map(PrimitiveMessageIndex)
        .unwrap_or_else(|| panic!("Primitive \"{}\" must exists", name))
}

pub fn inputs<const N: usize>(
    ctx: &mut PrimitiveContext,
) -> [Handle<Value>; N] {
    // SAFETY: this requires a bounds check befor, but I am the boundcer
    unsafe { *(ctx.inputs.as_ptr() as *const [Handle<Value>; N]) }
}

pub fn outputs<const N: usize>(
    ctx: &mut PrimitiveContext,
    values: [Handle<Value>; N],
) {
    // SAFETY: this requires a bounds check before, but I am the boundcer
    unsafe {
        std::ptr::copy_nonoverlapping(
            values.as_ptr(),
            ctx.outputs.as_mut_ptr(),
            N,
        );
    }
}

pub fn bool_object(ctx: &PrimitiveContext, cond: bool) -> Handle<Value> {
    match cond {
        true => ctx.vm.shared.specials.true_object.into(),
        false => ctx.vm.shared.specials.false_object.into(),
    }
}

impl From<PrimitiveMessageIndex> for u32 {
    fn from(value: PrimitiveMessageIndex) -> Self {
        value.as_raw() as u32
    }
}
