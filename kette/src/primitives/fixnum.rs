use std::ops::Neg;

use crate::{
    primitives::bool_object, Allocator, ExecutionResult, NumberError,
    PrimitiveContext, Tagged, Value,
};

use crate::primitives::ratio::make_ratio_from_values;

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

fn output_checked_i64(
    ctx: &mut PrimitiveContext,
    value: Option<i64>,
    overflow: impl FnOnce() -> i128,
) -> ExecutionResult {
    if let Some(res) = value {
        let tagged = Tagged::<i64>::new_value(res);
        ctx.outputs[0] = tagged.into();
        return ExecutionResult::Normal;
    }
    let big = ctx.heap.allocate_bignum_from_i128(overflow());
    ctx.outputs[0] = big.into();
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
    let b = unsafe { ctx.receiver.as_fixnum::<i64>() };
    let a = unsafe { arg.as_fixnum::<i64>() };
    output_checked_i64(ctx, a.checked_add(b), || (a as i128) + (b as i128))
}

pub fn fixnum_sub(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let arg = ctx.inputs[0];
    let b = unsafe { ctx.receiver.as_fixnum::<i64>() };
    let a = unsafe { arg.as_fixnum::<i64>() };
    output_checked_i64(ctx, a.checked_sub(b), || (a as i128) - (b as i128))
}

// one right shift could be enough, but we limit ourself then by 1 extra bit space.
// not much, maybe remove the untagging and promote to bignum.
pub fn fixnum_mul(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let arg = ctx.inputs[0];
    let b = unsafe { ctx.receiver.as_fixnum::<i64>() };
    let a = unsafe { arg.as_fixnum::<i64>() };
    output_checked_i64(ctx, a.checked_mul(b), || (a as i128) * (b as i128))
}

pub fn fixnum_div(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let b = unsafe { ctx.receiver.as_fixnum::<i64>() };
    let a = unsafe { ctx.inputs[0].as_fixnum::<i64>() };

    if b == 0 {
        return ExecutionResult::NumberError(NumberError::DivisionByZero);
    }
    if a % b == 0 {
        return output_checked_i64(ctx, a.checked_div(b), || {
            (a as i128) / (b as i128)
        });
    }

    match make_ratio_from_values(
        ctx.heap,
        Value::from_fixnum(a),
        Value::from_fixnum(b),
    ) {
        Ok(res) => ctx.outputs[0] = res,
        Err(err) => return ExecutionResult::NumberError(err),
    }
    ExecutionResult::Normal
}

pub fn fixnum_mod(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let arg = ctx.inputs[0];
    let b = unsafe { ctx.receiver.as_fixnum::<i64>() };
    let a = unsafe { arg.as_fixnum::<i64>() };
    if b == 0 {
        return ExecutionResult::NumberError(NumberError::DivisionByZero);
    }
    output_checked_i64(ctx, a.checked_rem(b), || (a as i128) % (b as i128))
}

pub fn fixnum_pow(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let arg = ctx.inputs[0];
    let b = unsafe { ctx.receiver.as_fixnum::<i64>() };
    let a = unsafe { arg.as_fixnum::<i64>() };
    if b < 0 {
        return ExecutionResult::NumberError(NumberError::Overflow);
    }
    let exp = b as u32;
    if let Some(res) = a.checked_pow(exp) {
        let tagged = Tagged::<i64>::new_value(res);
        ctx.outputs[0] = tagged.into();
        return ExecutionResult::Normal;
    }
    let base = a as i128;
    match base.checked_pow(exp) {
        Some(res) => {
            let big = ctx.heap.allocate_bignum_from_i128(res);
            ctx.outputs[0] = big.into();
            ExecutionResult::Normal
        }
        None => ExecutionResult::NumberError(NumberError::Overflow),
    }
}

pub fn fixnum_neg(ctx: &mut PrimitiveContext) -> ExecutionResult {
    // SAFETY: receiver must be valid fixnum
    let value = unsafe { ctx.receiver.as_fixnum::<i64>() };
    output_checked_i64(ctx, value.checked_neg(), || -(value as i128))
}

pub fn fixnum_and(ctx: &mut PrimitiveContext) -> ExecutionResult {
    fixnum_binop(ctx, |_, a, b| {
        let (a, b) = (a.raw_i64(), b.raw_i64());
        let res = a & b;
        let res = Tagged::from_raw(res);
        Ok(res)
    })
}

pub fn fixnum_or(ctx: &mut PrimitiveContext) -> ExecutionResult {
    fixnum_binop(ctx, |_, a, b| {
        let (a, b) = (a.raw_i64(), b.raw_i64());
        let res = a | b;
        let res = Tagged::from_raw(res);
        Ok(res)
    })
}

pub fn fixnum_eq(ctx: &mut PrimitiveContext) -> ExecutionResult {
    fixnum_logic_binop(ctx, |_, a, b| {
        let (a, b) = (a.raw_i64(), b.raw_i64());
        let res = a == b;
        Ok(res)
    })
}

pub fn fixnum_neq(ctx: &mut PrimitiveContext) -> ExecutionResult {
    fixnum_logic_binop(ctx, |_, a, b| {
        let (a, b) = (a.raw_i64(), b.raw_i64());
        let res = a != b;
        Ok(res)
    })
}

pub fn fixnum_lt(ctx: &mut PrimitiveContext) -> ExecutionResult {
    fixnum_logic_binop(ctx, |_, a, b| {
        let (a, b) = (a.raw_i64(), b.raw_i64());
        let res = a < b;
        Ok(res)
    })
}

pub fn fixnum_gt(ctx: &mut PrimitiveContext) -> ExecutionResult {
    fixnum_logic_binop(ctx, |_, a, b| {
        let (a, b) = (a.raw_i64(), b.raw_i64());
        let res = a > b;
        Ok(res)
    })
}

pub fn fixnum_leq(ctx: &mut PrimitiveContext) -> ExecutionResult {
    fixnum_logic_binop(ctx, |_, a, b| {
        let (a, b) = (a.raw_i64(), b.raw_i64());
        let res = a <= b;
        Ok(res)
    })
}

pub fn fixnum_geq(ctx: &mut PrimitiveContext) -> ExecutionResult {
    fixnum_logic_binop(ctx, |_, a, b| {
        let (a, b) = (a.raw_i64(), b.raw_i64());
        let res = a >= b;
        Ok(res)
    })
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
