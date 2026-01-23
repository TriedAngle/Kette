use std::ops::Neg;

use crate::{
    primitives::bool_object, Allocator, ExecutionResult, NumberError,
    PrimitiveContext, Tagged,
};

// TODO: handle overflows and/or promotion

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
    fixnum_binop(ctx, |_, a, b| {
        let (a, b) = (a.raw_i64(), b.raw_i64());
        let res = a + b;
        let res = Tagged::from_raw(res);
        Ok(res)
    })
}

pub fn fixnum_sub(ctx: &mut PrimitiveContext) -> ExecutionResult {
    fixnum_binop(ctx, |_, a, b| {
        let (a, b) = (a.raw_i64(), b.raw_i64());
        let res = a - b;
        let res = Tagged::from_raw(res);
        Ok(res)
    })
}

// one right shift could be enough, but we limit ourself then by 1 extra bit space.
// not much, maybe remove the untagging and promote to bignum.
pub fn fixnum_mul(ctx: &mut PrimitiveContext) -> ExecutionResult {
    fixnum_binop(ctx, |_, a, b| {
        let (a, b) = (a.as_i64(), b.as_i64());
        let res = a * b;
        let res = Tagged::new_value(res);
        Ok(res)
    })
}

pub fn fixnum_div(ctx: &mut PrimitiveContext) -> ExecutionResult {
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

pub fn fixnum_mod(ctx: &mut PrimitiveContext) -> ExecutionResult {
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

pub fn fixnum_pow(ctx: &mut PrimitiveContext) -> ExecutionResult {
    fixnum_binop(ctx, |_, a, b| {
        let (a, b) = (a.as_i64(), b.as_i64());
        let res = a.pow(b as u32);
        let res = Tagged::new_value(res);
        Ok(res)
    })
}

pub fn fixnum_neg(ctx: &mut PrimitiveContext) -> ExecutionResult {
    // SAFETY: receiver must be valid fixnum
    let value = unsafe { ctx.receiver.as_fixnum::<i64>() };
    let neg = value.neg();
    let res = Tagged::<i64>::new_value(neg);
    ctx.outputs[0] = res.into();
    ExecutionResult::Normal
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
    // SAFETY: no gc here
    ctx.outputs[0] = ba.into();
    ExecutionResult::Normal
}

pub fn parent(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let p = ctx.vm.specials().fixnum_traits;
    ctx.outputs[0] = p.into();
    ExecutionResult::Normal
}
