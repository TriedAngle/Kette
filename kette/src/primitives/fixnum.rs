use std::ops::Neg;

use crate::{ExecutionResult, PrimitiveContext, TaggedI64, execution::IntegerError};

// TODO: handle overflows and/or promotion

type Fixnum2Op =
    fn(ctx: &mut PrimitiveContext, a: TaggedI64, b: TaggedI64) -> Result<TaggedI64, IntegerError>;

fn fixnum_binop(ctx: &mut PrimitiveContext, op: Fixnum2Op) -> ExecutionResult {
    let a = TaggedI64::from(ctx.receiver);
    let b = TaggedI64::from(ctx.arguments[0]);
    match op(ctx, a, b) {
        Ok(res) => ctx.result[0] = res.into(),
        Err(err) => return ExecutionResult::IntegerError(err),
    }
    ExecutionResult::Normal
}

// TODO: duplication is silly, maybe another trait
type Fixnum2LogicOp =
    fn(ctx: &mut PrimitiveContext, a: TaggedI64, b: TaggedI64) -> Result<bool, IntegerError>;
fn fixnum_logic_binop(ctx: &mut PrimitiveContext, op: Fixnum2LogicOp) -> ExecutionResult {
    let a = TaggedI64::from(ctx.receiver);
    let b = TaggedI64::from(ctx.arguments[0]);
    match op(ctx, a, b) {
        Ok(res) => {
            if res {
                ctx.result[0] = ctx.vm.shared.specials.true_object.into();
            } else {
                ctx.result[0] = ctx.vm.shared.specials.false_object.into();
            }
        }
        Err(err) => return ExecutionResult::IntegerError(err),
    }
    ExecutionResult::Normal
}

pub fn fixnum_add(ctx: &mut PrimitiveContext) -> ExecutionResult {
    fixnum_binop(ctx, |_, a, b| {
        let res = a + b;
        Ok(res)
    })
}

pub fn fixnum_sub(ctx: &mut PrimitiveContext) -> ExecutionResult {
    fixnum_binop(ctx, |_, a, b| {
        let res = a - b;
        Ok(res)
    })
}

// one right shift could be enough, but we limit ourself then by 1 extra bit space.
// not much, maybe remove the untagging and promote to bignum.
pub fn fixnum_mul(ctx: &mut PrimitiveContext) -> ExecutionResult {
    fixnum_binop(ctx, |_, a, b| {
        let (a, b) = (a.to_i64(), b.to_i64());
        let res = a * b;
        let res = TaggedI64::new(res);
        Ok(res)
    })
}

pub fn fixnum_div(ctx: &mut PrimitiveContext) -> ExecutionResult {
    fixnum_binop(ctx, |_, a, b| {
        if b.raw() == 0 {
            return Err(IntegerError::DivisionByZero);
        }
        let (a, b) = (a.raw(), b.raw());
        let res = a / b;
        let res = TaggedI64::new(res);
        Ok(res)
    })
}

pub fn fixnum_mod(ctx: &mut PrimitiveContext) -> ExecutionResult {
    fixnum_binop(ctx, |_, a, b| {
        let (a, b) = (a.raw(), b.raw());
        let res = a % b;
        let res = TaggedI64::from_raw_tagged(res);
        Ok(res)
    })
}

pub fn fixnum_neg(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let value = TaggedI64::from(ctx.receiver);
    let value = value.to_i64();
    let neg = value.neg();
    let res = TaggedI64::new(neg);
    ctx.result[0] = res.into();
    ExecutionResult::Normal
}

pub fn fixnum_and(ctx: &mut PrimitiveContext) -> ExecutionResult {
    fixnum_binop(ctx, |_, a, b| {
        let (a, b) = (a.raw(), b.raw());
        let res = a & b;
        let res = TaggedI64::from_raw_tagged(res);
        Ok(res)
    })
}

pub fn fixnum_or(ctx: &mut PrimitiveContext) -> ExecutionResult {
    fixnum_binop(ctx, |_, a, b| {
        let (a, b) = (a.raw(), b.raw());
        let res = a | b;
        let res = TaggedI64::from_raw_tagged(res);
        Ok(res)
    })
}

pub fn fixnum_eq(ctx: &mut PrimitiveContext) -> ExecutionResult {
    fixnum_logic_binop(ctx, |_, a, b| {
        let (a, b) = (a.raw(), b.raw());
        let res = a == b;
        Ok(res)
    })
}

pub fn fixnum_neq(ctx: &mut PrimitiveContext) -> ExecutionResult {
    fixnum_logic_binop(ctx, |_, a, b| {
        let (a, b) = (a.raw(), b.raw());
        let res = a != b;
        Ok(res)
    })
}

pub fn fixnum_lt(ctx: &mut PrimitiveContext) -> ExecutionResult {
    fixnum_logic_binop(ctx, |_, a, b| {
        let (a, b) = (a.raw(), b.raw());
        let res = a < b;
        Ok(res)
    })
}

pub fn fixnum_gt(ctx: &mut PrimitiveContext) -> ExecutionResult {
    fixnum_logic_binop(ctx, |_, a, b| {
        let (a, b) = (a.raw(), b.raw());
        let res = a > b;
        Ok(res)
    })
}

pub fn fixnum_leq(ctx: &mut PrimitiveContext) -> ExecutionResult {
    fixnum_logic_binop(ctx, |_, a, b| {
        let (a, b) = (a.raw(), b.raw());
        let res = a <= b;
        Ok(res)
    })
}

pub fn fixnum_geq(ctx: &mut PrimitiveContext) -> ExecutionResult {
    fixnum_logic_binop(ctx, |_, a, b| {
        let (a, b) = (a.raw(), b.raw());
        let res = a >= b;
        Ok(res)
    })
}
