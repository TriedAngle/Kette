use std::mem;

use crate::{
    ExecutionResult, ExecutionState, Handle, HeapProxy, Interpreter,
    ThreadProxy, VMProxy, Value,
};

mod alien;
mod array;
mod bignum;
mod bytearray;
mod error;
mod fixnum;
mod float;
mod general;
mod message;
mod method;
mod parsing;
mod quotation;
mod ratio;
mod stack;
mod string;
mod threads;
mod vector;
pub use vector::Vector;

#[repr(transparent)]
#[derive(Debug, Copy, Clone)]
pub struct PrimitiveMessageIndex(usize);

impl PrimitiveMessageIndex {
    /// # Safety
    /// id must be a valid primitive id
    #[must_use]
    pub unsafe fn from_usize(id: usize) -> Self {
        Self(id)
    }

    #[must_use]
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
    PrimitiveMessage::new("dup", 0, 2, stack::dup),
    PrimitiveMessage::new("2dup", 1, 4, stack::dup2),
    PrimitiveMessage::new("drop", 0, 0, stack::drop),
    PrimitiveMessage::new("2drop", 1, 0, stack::drop2),
    PrimitiveMessage::new("3drop", 2, 0, stack::drop3),
    PrimitiveMessage::new("swap", 1, 2, stack::swap),
    PrimitiveMessage::new("over", 1, 3, stack::over),

    PrimitiveMessage::new("pick", 2, 4, stack::pick),
    PrimitiveMessage::new("rot", 2, 3, stack::rot),
    PrimitiveMessage::new("-rot", 2, 3, stack::neg_rot),
    PrimitiveMessage::new("spin", 2, 3, stack::spin),
    PrimitiveMessage::new("dupd", 1, 3, stack::dupd),
    PrimitiveMessage::new("dropd", 1, 1, stack::dropd),
    PrimitiveMessage::new("2dropd", 2, 1, stack::dropd2),
    PrimitiveMessage::new("swapd", 2, 3, stack::swapd),
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
    PrimitiveMessage::new("fixnum+Unchecked", 1, 1, fixnum::fixnum_add_unchecked),
    PrimitiveMessage::new("fixnum-Unchecked", 1, 1, fixnum::fixnum_sub_unchecked),
    PrimitiveMessage::new("fixnum*Unchecked", 1, 1, fixnum::fixnum_mul_unchecked),
    PrimitiveMessage::new("fixnum/Unchecked", 1, 1, fixnum::fixnum_div_unchecked),
    PrimitiveMessage::new("fixnum%Unchecked", 1, 1, fixnum::fixnum_mod_unchecked),
    PrimitiveMessage::new("fixnum^Unchecked", 1, 1, fixnum::fixnum_pow_unchecked),
    PrimitiveMessage::new("fixnumNegUnchecked", 0, 1, fixnum::fixnum_neg_unchecked),
    PrimitiveMessage::new("fixnumBitAnd", 1, 1, fixnum::fixnum_and),
    PrimitiveMessage::new("fixnumBitOr", 1, 1, fixnum::fixnum_or),
    PrimitiveMessage::new("fixnum=", 1, 1, fixnum::fixnum_eq),
    PrimitiveMessage::new("fixnum!=", 1, 1, fixnum::fixnum_neq),
    PrimitiveMessage::new("fixnum<", 1, 1, fixnum::fixnum_lt),
    PrimitiveMessage::new("fixnum>", 1, 1, fixnum::fixnum_gt),
    PrimitiveMessage::new("fixnum<=", 1, 1, fixnum::fixnum_leq),
    PrimitiveMessage::new("fixnum>=", 1, 1, fixnum::fixnum_geq),
    PrimitiveMessage::new("fixnum>string", 0, 1, fixnum::fixnum_to_utf8_bytes),
    PrimitiveMessage::new("fixnum>ratio", 0, 1, ratio::fixnum_to_ratio),
    PrimitiveMessage::new("fixnum>float", 0, 1, fixnum::fixnum_to_float),
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
    PrimitiveMessage::new("float>bignum", 0, 1, float::float_to_bignum),
    PrimitiveMessage::new("floatParent", 0, 1, float::parent),
    // Bignum
    PrimitiveMessage::new("fixnum>bignum", 0, 1, bignum::fixnum_to_bignum),
    PrimitiveMessage::new("bignumToFixnumChecked", 0, 1, bignum::bignum_to_fixnum_checked),
    PrimitiveMessage::new("bignum>float", 0, 1, bignum::bignum_to_float),
    PrimitiveMessage::new("bignum>ratio", 0, 1, ratio::bignum_to_ratio),
    PrimitiveMessage::new("bignum+", 1, 1, bignum::bignum_add),
    PrimitiveMessage::new("bignum-", 1, 1, bignum::bignum_sub),
    PrimitiveMessage::new("bignum*", 1, 1, bignum::bignum_mul),
    PrimitiveMessage::new("bignum/", 1, 1, bignum::bignum_div),
    PrimitiveMessage::new("bignum%", 1, 1, bignum::bignum_mod),
    PrimitiveMessage::new("bignumNeg", 0, 1, bignum::bignum_neg),
    PrimitiveMessage::new("bignum=", 1, 1, bignum::bignum_eq),
    PrimitiveMessage::new("bignum!=", 1, 1, bignum::bignum_neq),
    PrimitiveMessage::new("bignum<", 1, 1, bignum::bignum_lt),
    PrimitiveMessage::new("bignum>", 1, 1, bignum::bignum_gt),
    PrimitiveMessage::new("bignum<=", 1, 1, bignum::bignum_leq),
    PrimitiveMessage::new("bignum>=", 1, 1, bignum::bignum_geq),
    PrimitiveMessage::new("bignumParent", 0, 1, bignum::parent),
    // Ratio
    PrimitiveMessage::new("ratio?", 0, 1, ratio::is_ratio),
    PrimitiveMessage::new("2ratio?", 1, 1, ratio::is_2ratio),
    PrimitiveMessage::new("ratioNew", 1, 1, ratio::ratio_new),
    PrimitiveMessage::new("ratioNumerator", 0, 1, ratio::ratio_numerator),
    PrimitiveMessage::new("ratioDenominator", 0, 1, ratio::ratio_denominator),
    PrimitiveMessage::new("ratio>fixnum", 0, 1, ratio::ratio_to_fixnum),
    PrimitiveMessage::new("ratio+", 1, 1, ratio::ratio_add),
    PrimitiveMessage::new("ratio-", 1, 1, ratio::ratio_sub),
    PrimitiveMessage::new("ratio*", 1, 1, ratio::ratio_mul),
    PrimitiveMessage::new("ratio/", 1, 1, ratio::ratio_div),
    PrimitiveMessage::new("ratioNeg", 0, 1, ratio::ratio_neg),
    PrimitiveMessage::new("ratio=", 1, 1, ratio::ratio_eq),
    PrimitiveMessage::new("ratio!=", 1, 1, ratio::ratio_neq),
    PrimitiveMessage::new("ratio<", 1, 1, ratio::ratio_lt),
    PrimitiveMessage::new("ratio>", 1, 1, ratio::ratio_gt),
    PrimitiveMessage::new("ratio<=", 1, 1, ratio::ratio_leq),
    PrimitiveMessage::new("ratio>=", 1, 1, ratio::ratio_geq),
    PrimitiveMessage::new("ratio>float", 0, 1, ratio::ratio_to_float),
    PrimitiveMessage::new("ratio>string", 0, 1, ratio::ratio_to_string),
    PrimitiveMessage::new("ratioParent", 0, 1, ratio::parent),
    // Alien
    PrimitiveMessage::new("alienU8At", 1, 1, alien::alien_u8_at),
    PrimitiveMessage::new("alienI8At", 1, 1, alien::alien_i8_at),
    PrimitiveMessage::new("alienU16At", 1, 1, alien::alien_u16_at),
    PrimitiveMessage::new("alienI16At", 1, 1, alien::alien_i16_at),
    PrimitiveMessage::new("alienU32At", 1, 1, alien::alien_u32_at),
    PrimitiveMessage::new("alienI32At", 1, 1, alien::alien_i32_at),
    PrimitiveMessage::new("alienU64At", 1, 1, alien::alien_u64_at),
    PrimitiveMessage::new("alienI64At", 1, 1, alien::alien_i64_at),
    PrimitiveMessage::new("alienU8AtPut", 2, 0, alien::alien_u8_at_put),
    PrimitiveMessage::new("alienI8AtPut", 2, 0, alien::alien_i8_at_put),
    PrimitiveMessage::new("alienU16AtPut", 2, 0, alien::alien_u16_at_put),
    PrimitiveMessage::new("alienI16AtPut", 2, 0, alien::alien_i16_at_put),
    PrimitiveMessage::new("alienU32AtPut", 2, 0, alien::alien_u32_at_put),
    PrimitiveMessage::new("alienI32AtPut", 2, 0, alien::alien_i32_at_put),
    PrimitiveMessage::new("alienU64AtPut", 2, 0, alien::alien_u64_at_put),
    PrimitiveMessage::new("alienI64AtPut", 2, 0, alien::alien_i64_at_put),
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
    PrimitiveMessage::new("bytearray>string", 0, 1, bytearray::bytearray_to_string),
    PrimitiveMessage::new("bytearrayU16At", 1, 1, bytearray::bytearray_u16_at),
    PrimitiveMessage::new("bytearrayI16At", 1, 1, bytearray::bytearray_i16_at),
    PrimitiveMessage::new("bytearrayU32At", 1, 1, bytearray::bytearray_u32_at),
    PrimitiveMessage::new("bytearrayI32At", 1, 1, bytearray::bytearray_i32_at),
    PrimitiveMessage::new("bytearrayU64At", 1, 1, bytearray::bytearray_u64_at),
    PrimitiveMessage::new("bytearrayI64At", 1, 1, bytearray::bytearray_i64_at),
    PrimitiveMessage::new("bytearrayU16AtPut", 2, 0, bytearray::bytearray_u16_at_put),
    PrimitiveMessage::new("bytearrayI16AtPut", 2, 0, bytearray::bytearray_i16_at_put),
    PrimitiveMessage::new("bytearrayU32AtPut", 2, 0, bytearray::bytearray_u32_at_put),
    PrimitiveMessage::new("bytearrayI32AtPut", 2, 0, bytearray::bytearray_i32_at_put),
    PrimitiveMessage::new("bytearrayU64AtPut", 2, 0, bytearray::bytearray_u64_at_put),
    PrimitiveMessage::new("bytearrayI64AtPut", 2, 0, bytearray::bytearray_i64_at_put),
    PrimitiveMessage::new("stringParent", 0, 1, string::parent),
    PrimitiveMessage::new("stringSize", 0, 1, string::size),
    PrimitiveMessage::new("string>bytearray", 0, 1, string::string_to_bytearray),
    PrimitiveMessage::new("string>message", 0, 1, string::string_to_message),
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
    PrimitiveMessage::new("{", 1, 1, parsing::parse_array),
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

#[must_use]
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
