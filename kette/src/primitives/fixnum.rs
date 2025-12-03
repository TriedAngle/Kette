use std::ops::Neg;

use crate::{ExecutionResult, Handle, IntegerError, PrimitiveContext, Tagged, Value};

// TODO: handle overflows and/or promotion

type Fixnum2Op = fn(
    ctx: &mut PrimitiveContext,
    a: Tagged<i64>,
    b: Tagged<i64>,
) -> Result<Tagged<i64>, IntegerError>;

fn fixnum_binop(ctx: &mut PrimitiveContext<'_, '_>, op: Fixnum2Op) -> ExecutionResult {
    let a = unsafe { ctx.receiver.as_tagged::<i64>() };
    let b = unsafe { ctx.arguments[0].as_tagged::<i64>() };
    match op(ctx, a, b) {
        Ok(res) => ctx.result[0] = res.into(),
        Err(err) => return ExecutionResult::IntegerError(err),
    }
    ExecutionResult::Normal
}

type Fixnum2LogicOp =
    fn(ctx: &mut PrimitiveContext, a: Tagged<i64>, b: Tagged<i64>) -> Result<bool, IntegerError>;
fn fixnum_logic_binop(ctx: &mut PrimitiveContext, op: Fixnum2LogicOp) -> ExecutionResult {
    let a = unsafe { ctx.receiver.as_tagged::<i64>() };
    let b = unsafe { ctx.arguments[0].as_tagged::<i64>() };
    match op(ctx, a, b) {
        Ok(res) => ctx.result[0] = bool_object(ctx, res),
        Err(err) => return ExecutionResult::IntegerError(err),
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
        let res = a + b;
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
        let res = Tagged::from_raw(res);
        Ok(res)
    })
}

pub fn fixnum_div(ctx: &mut PrimitiveContext) -> ExecutionResult {
    fixnum_binop(ctx, |_, a, b| {
        if b.raw() == 0 {
            return Err(IntegerError::DivisionByZero);
        }
        let (a, b) = (a.raw_i64(), b.raw_i64());
        let res = a / b;
        let res = Tagged::from_raw(res);
        Ok(res)
    })
}

pub fn fixnum_mod(ctx: &mut PrimitiveContext) -> ExecutionResult {
    fixnum_binop(ctx, |_, a, b| {
        let (a, b) = (a.raw_i64(), b.raw_i64());
        let res = a % b;
        let res = Tagged::from_raw(res);
        Ok(res)
    })
}

pub fn fixnum_neg(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let value = unsafe { ctx.receiver.as_fixnum::<i64>() };
    let neg = value.neg();
    let res = Tagged::<i64>::new_value(neg);
    ctx.result[0] = res.into();
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
    ctx.result[0] = bool_object(ctx, is_a);
    ExecutionResult::Normal
}

pub fn is_2fixnum(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let is_a = ctx.receiver.inner().is_fixnum();
    let is_b = ctx.arguments[0].inner().is_fixnum();
    ctx.result[0] = bool_object(ctx, is_a && is_b);
    ExecutionResult::Normal
}

fn bool_object(ctx: &PrimitiveContext, cond: bool) -> Handle<Value> {
    match cond {
        true => ctx.vm.shared.specials.true_object.into(),
        false => ctx.vm.shared.specials.false_object.into(),
    }
}
