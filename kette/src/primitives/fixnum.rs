use std::ops::Neg;

use std::cmp::Ordering;

use crate::{
    Allocator, BigNum, ExecutionResult, NumberError, ObjectType,
    PrimitiveContext, Tagged, Value,
    primitives::bignum::{
        bignum_add_raw, bignum_mul_raw, bignum_sub_raw, cmp_bignum,
    },
    primitives::bool_object,
};

const FIXNUM_MIN: i128 = -(1_i128 << 62);
const FIXNUM_MAX: i128 = (1_i128 << 62) - 1;

type Fixnum2Op = fn(
    ctx: &mut PrimitiveContext,
    a: Tagged<i64>,
    b: Tagged<i64>,
) -> Result<Tagged<i64>, NumberError>;

fn fixnum_binop(
    ctx: &mut PrimitiveContext<'_, '_>,
    op: Fixnum2Op,
) -> ExecutionResult {
    let b = ctx.receiver.as_tagged::<i64>();
    let a = ctx.inputs[0].as_tagged::<i64>();
    match op(ctx, a, b) {
        Ok(res) => ctx.outputs[0] = res.into(),
        Err(err) => return ExecutionResult::NumberError(err),
    }
    ExecutionResult::Normal
}

fn output_i128(ctx: &mut PrimitiveContext, value: i128) -> ExecutionResult {
    if value < FIXNUM_MIN || value > FIXNUM_MAX {
        let big = ctx.heap.allocate_bignum_from_i128(value);
        ctx.outputs[0] = big.into();
        return ExecutionResult::Normal;
    }
    let res = Tagged::<i64>::new_value(value as i64);
    ctx.outputs[0] = res.into();
    ExecutionResult::Normal
}

fn arg_as_bignum(
    ctx: &mut PrimitiveContext,
    value: crate::Handle<Value>,
    name: &str,
) -> Result<crate::Handle<BigNum>, ExecutionResult> {
    if value.inner().is_fixnum() {
        let fix = unsafe { value.as_fixnum::<i64>() };
        return Ok(ctx.heap.allocate_bignum_from_i64(fix));
    }
    if value.inner().is_object() {
        let obj = unsafe { value.inner().as_heap_handle_unchecked() };
        if obj.header.object_type() == Some(ObjectType::BigNum) {
            return Ok(unsafe { obj.cast::<BigNum>() });
        }
    }
    Err(ExecutionResult::Panic(format!(
        "{name}: expected fixnum or bignum"
    )))
}

fn promote_fixnum(ctx: &mut PrimitiveContext) -> crate::Handle<BigNum> {
    let value = unsafe { ctx.receiver.as_fixnum::<i64>() };
    ctx.heap.allocate_bignum_from_i64(value)
}

fn output_bignum_or_fixnum(
    ctx: &mut PrimitiveContext,
    value: crate::Handle<BigNum>,
) -> ExecutionResult {
    if let Some(fix) = value.to_fixnum_checked() {
        ctx.outputs[0] =
            unsafe { Value::from_fixnum(fix).as_handle_unchecked() };
    } else {
        ctx.outputs[0] = value.into();
    }
    ExecutionResult::Normal
}

type Fixnum2LogicOp = fn(
    ctx: &mut PrimitiveContext,
    a: Tagged<i64>,
    b: Tagged<i64>,
) -> Result<bool, NumberError>;
fn fixnum_logic_binop(
    ctx: &mut PrimitiveContext,
    op: Fixnum2LogicOp,
) -> ExecutionResult {
    let b = ctx.receiver.as_tagged::<i64>();
    let a = ctx.inputs[0].as_tagged::<i64>();
    match op(ctx, a, b) {
        Ok(res) => ctx.outputs[0] = bool_object(ctx, res),
        Err(err) => return ExecutionResult::NumberError(err),
    }
    ExecutionResult::Normal
}

pub fn fixnum_add(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let arg = ctx.inputs[0];
    if arg.inner().is_fixnum() {
        let b = unsafe { ctx.receiver.as_fixnum::<i64>() };
        let a = unsafe { arg.as_fixnum::<i64>() };
        let res = (a as i128) + (b as i128);
        return output_i128(ctx, res);
    }
    let a = match arg_as_bignum(ctx, arg, "fixnum+") {
        Ok(value) => value,
        Err(err) => return err,
    };
    let b = promote_fixnum(ctx);
    let result = bignum_add_raw(ctx.heap, &a, &b);
    output_bignum_or_fixnum(ctx, result)
}

pub fn fixnum_sub(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let arg = ctx.inputs[0];
    if arg.inner().is_fixnum() {
        let b = unsafe { ctx.receiver.as_fixnum::<i64>() };
        let a = unsafe { arg.as_fixnum::<i64>() };
        let res = (a as i128) - (b as i128);
        return output_i128(ctx, res);
    }
    let a = match arg_as_bignum(ctx, arg, "fixnum-") {
        Ok(value) => value,
        Err(err) => return err,
    };
    let b = promote_fixnum(ctx);
    let result = bignum_sub_raw(ctx.heap, &a, &b);
    output_bignum_or_fixnum(ctx, result)
}

// one right shift could be enough, but we limit ourself then by 1 extra bit space.
// not much, maybe remove the untagging and promote to bignum.
pub fn fixnum_mul(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let arg = ctx.inputs[0];
    if arg.inner().is_fixnum() {
        let b = unsafe { ctx.receiver.as_fixnum::<i64>() };
        let a = unsafe { arg.as_fixnum::<i64>() };
        let res = (a as i128) * (b as i128);
        return output_i128(ctx, res);
    }
    let a = match arg_as_bignum(ctx, arg, "fixnum*") {
        Ok(value) => value,
        Err(err) => return err,
    };
    let b = promote_fixnum(ctx);
    let result = bignum_mul_raw(ctx.heap, &a, &b);
    output_bignum_or_fixnum(ctx, result)
}

pub fn fixnum_div(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let arg = ctx.inputs[0];
    if !arg.inner().is_fixnum() {
        return ExecutionResult::Panic(
            "fixnum/: bignum division not implemented".to_string(),
        );
    }
    let b = unsafe { ctx.receiver.as_fixnum::<i64>() };
    let a = unsafe { arg.as_fixnum::<i64>() };
    if b == 0 {
        return ExecutionResult::NumberError(NumberError::DivisionByZero);
    }
    let res = (a as i128) / (b as i128);
    output_i128(ctx, res)
}

pub fn fixnum_mod(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let arg = ctx.inputs[0];
    if !arg.inner().is_fixnum() {
        return ExecutionResult::Panic(
            "fixnum%: bignum modulus not implemented".to_string(),
        );
    }
    let b = unsafe { ctx.receiver.as_fixnum::<i64>() };
    let a = unsafe { arg.as_fixnum::<i64>() };
    if b == 0 {
        return ExecutionResult::NumberError(NumberError::DivisionByZero);
    }
    let res = (a as i128) % (b as i128);
    output_i128(ctx, res)
}

pub fn fixnum_pow(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let arg = ctx.inputs[0];
    if !arg.inner().is_fixnum() {
        return ExecutionResult::Panic(
            "fixnum^: bignum exponentiation not implemented".to_string(),
        );
    }
    let b = unsafe { ctx.receiver.as_fixnum::<i64>() };
    let a = unsafe { arg.as_fixnum::<i64>() };
    if b < 0 {
        return ExecutionResult::NumberError(NumberError::Overflow);
    }
    let exp = b as u32;
    let base = a as i128;
    match base.checked_pow(exp) {
        Some(res) => output_i128(ctx, res),
        None => ExecutionResult::NumberError(NumberError::Overflow),
    }
}

pub fn fixnum_neg(ctx: &mut PrimitiveContext) -> ExecutionResult {
    // SAFETY: receiver must be valid fixnum
    let value = unsafe { ctx.receiver.as_fixnum::<i64>() };
    let neg = -(value as i128);
    output_i128(ctx, neg)
}

pub fn fixnum_and(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let arg = ctx.inputs[0];
    if !arg.inner().is_fixnum() {
        return ExecutionResult::Panic(
            "fixnumBitAnd: expected fixnum".to_string(),
        );
    }
    fixnum_binop(ctx, |_, a, b| {
        let (a, b) = (a.raw_i64(), b.raw_i64());
        let res = a & b;
        let res = Tagged::from_raw(res);
        Ok(res)
    })
}

pub fn fixnum_or(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let arg = ctx.inputs[0];
    if !arg.inner().is_fixnum() {
        return ExecutionResult::Panic(
            "fixnumBitOr: expected fixnum".to_string(),
        );
    }
    fixnum_binop(ctx, |_, a, b| {
        let (a, b) = (a.raw_i64(), b.raw_i64());
        let res = a | b;
        let res = Tagged::from_raw(res);
        Ok(res)
    })
}

pub fn fixnum_eq(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let arg = ctx.inputs[0];
    if arg.inner().is_fixnum() {
        return fixnum_logic_binop(ctx, |_, a, b| {
            let (a, b) = (a.raw_i64(), b.raw_i64());
            let res = a == b;
            Ok(res)
        });
    }
    let a = match arg_as_bignum(ctx, arg, "fixnum=") {
        Ok(value) => value,
        Err(err) => return err,
    };
    let b = promote_fixnum(ctx);
    ctx.outputs[0] = bool_object(ctx, cmp_bignum(&a, &b) == Ordering::Equal);
    ExecutionResult::Normal
}

pub fn fixnum_neq(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let arg = ctx.inputs[0];
    if arg.inner().is_fixnum() {
        return fixnum_logic_binop(ctx, |_, a, b| {
            let (a, b) = (a.raw_i64(), b.raw_i64());
            let res = a != b;
            Ok(res)
        });
    }
    let a = match arg_as_bignum(ctx, arg, "fixnum!=") {
        Ok(value) => value,
        Err(err) => return err,
    };
    let b = promote_fixnum(ctx);
    ctx.outputs[0] = bool_object(ctx, cmp_bignum(&a, &b) != Ordering::Equal);
    ExecutionResult::Normal
}

pub fn fixnum_lt(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let arg = ctx.inputs[0];
    if arg.inner().is_fixnum() {
        return fixnum_logic_binop(ctx, |_, a, b| {
            let (a, b) = (a.raw_i64(), b.raw_i64());
            let res = a < b;
            Ok(res)
        });
    }
    let a = match arg_as_bignum(ctx, arg, "fixnum<") {
        Ok(value) => value,
        Err(err) => return err,
    };
    let b = promote_fixnum(ctx);
    ctx.outputs[0] = bool_object(ctx, cmp_bignum(&a, &b) == Ordering::Less);
    ExecutionResult::Normal
}

pub fn fixnum_gt(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let arg = ctx.inputs[0];
    if arg.inner().is_fixnum() {
        return fixnum_logic_binop(ctx, |_, a, b| {
            let (a, b) = (a.raw_i64(), b.raw_i64());
            let res = a > b;
            Ok(res)
        });
    }
    let a = match arg_as_bignum(ctx, arg, "fixnum>") {
        Ok(value) => value,
        Err(err) => return err,
    };
    let b = promote_fixnum(ctx);
    ctx.outputs[0] = bool_object(ctx, cmp_bignum(&a, &b) == Ordering::Greater);
    ExecutionResult::Normal
}

pub fn fixnum_leq(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let arg = ctx.inputs[0];
    if arg.inner().is_fixnum() {
        return fixnum_logic_binop(ctx, |_, a, b| {
            let (a, b) = (a.raw_i64(), b.raw_i64());
            let res = a <= b;
            Ok(res)
        });
    }
    let a = match arg_as_bignum(ctx, arg, "fixnum<=") {
        Ok(value) => value,
        Err(err) => return err,
    };
    let b = promote_fixnum(ctx);
    let ord = cmp_bignum(&a, &b);
    ctx.outputs[0] =
        bool_object(ctx, ord == Ordering::Less || ord == Ordering::Equal);
    ExecutionResult::Normal
}

pub fn fixnum_geq(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let arg = ctx.inputs[0];
    if arg.inner().is_fixnum() {
        return fixnum_logic_binop(ctx, |_, a, b| {
            let (a, b) = (a.raw_i64(), b.raw_i64());
            let res = a >= b;
            Ok(res)
        });
    }
    let a = match arg_as_bignum(ctx, arg, "fixnum>=") {
        Ok(value) => value,
        Err(err) => return err,
    };
    let b = promote_fixnum(ctx);
    let ord = cmp_bignum(&a, &b);
    ctx.outputs[0] =
        bool_object(ctx, ord == Ordering::Greater || ord == Ordering::Equal);
    ExecutionResult::Normal
}

pub fn is_fixnum(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let is_a = ctx.receiver.inner().is_fixnum();
    ctx.outputs[0] = bool_object(ctx, is_a);
    ExecutionResult::Normal
}

pub fn is_2fixnum(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let is_a = ctx.receiver.inner().is_fixnum();
    let is_b = ctx.inputs[0].inner().is_fixnum();
    ctx.outputs[0] = bool_object(ctx, is_a && is_b);
    ExecutionResult::Normal
}

pub fn fixnum_to_utf8_bytes(ctx: &mut PrimitiveContext) -> ExecutionResult {
    // SAFETY: receiver must be valid fixnum
    let value = unsafe { ctx.receiver.as_fixnum::<i64>() };
    let string = value.to_string();
    let ba = ctx.heap.allocate_aligned_bytearray(string.as_bytes(), 8);
    let string = ctx.heap.allocate_string(ba);
    // SAFETY: no gc here
    ctx.outputs[0] = string.into();
    ExecutionResult::Normal
}

pub fn fixnum_to_float(ctx: &mut PrimitiveContext) -> ExecutionResult {
    if !ctx.receiver.inner().is_fixnum() {
        return ExecutionResult::Panic(
            "fixnum>float: receiver must be a fixnum".to_string(),
        );
    }
    let value = unsafe { ctx.receiver.as_fixnum::<i64>() };
    let float = ctx.heap.allocate_float(value as f64);
    ctx.outputs[0] = float.into();
    ExecutionResult::Normal
}

pub fn fixnum_add_unchecked(ctx: &mut PrimitiveContext) -> ExecutionResult {
    fixnum_binop(ctx, |_, a, b| {
        let (a, b) = (a.raw_i64(), b.raw_i64());
        let res = a + b;
        let res = Tagged::from_raw(res);
        Ok(res)
    })
}

pub fn fixnum_sub_unchecked(ctx: &mut PrimitiveContext) -> ExecutionResult {
    fixnum_binop(ctx, |_, a, b| {
        let (a, b) = (a.raw_i64(), b.raw_i64());
        let res = a - b;
        let res = Tagged::from_raw(res);
        Ok(res)
    })
}

pub fn fixnum_mul_unchecked(ctx: &mut PrimitiveContext) -> ExecutionResult {
    fixnum_binop(ctx, |_, a, b| {
        let (a, b) = (a.as_i64(), b.as_i64());
        let res = a * b;
        let res = Tagged::new_value(res);
        Ok(res)
    })
}

pub fn fixnum_div_unchecked(ctx: &mut PrimitiveContext) -> ExecutionResult {
    fixnum_binop(ctx, |_, a, b| {
        let (a, b) = (a.as_i64(), b.as_i64());
        if b == 0 {
            return Err(NumberError::DivisionByZero);
        }
        let res = a / b;
        let res = Tagged::new_value(res);
        Ok(res)
    })
}

pub fn fixnum_mod_unchecked(ctx: &mut PrimitiveContext) -> ExecutionResult {
    fixnum_binop(ctx, |_, a, b| {
        let (a, b) = (a.raw_i64(), b.raw_i64());
        if b == 0 {
            return Err(NumberError::DivisionByZero);
        }
        let res = a % b;
        let res = Tagged::from_raw(res);
        Ok(res)
    })
}

pub fn fixnum_pow_unchecked(ctx: &mut PrimitiveContext) -> ExecutionResult {
    fixnum_binop(ctx, |_, a, b| {
        let (a, b) = (a.as_i64(), b.as_i64());
        let res = a.pow(b as u32);
        let res = Tagged::new_value(res);
        Ok(res)
    })
}

pub fn fixnum_neg_unchecked(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let value = unsafe { ctx.receiver.as_fixnum::<i64>() };
    let neg = value.neg();
    let res = Tagged::<i64>::new_value(neg);
    ctx.outputs[0] = res.into();
    ExecutionResult::Normal
}

pub fn parent(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let p = ctx.vm.specials().fixnum_traits;
    ctx.outputs[0] = p.into();
    ExecutionResult::Normal
}
