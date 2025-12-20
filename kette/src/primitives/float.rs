use crate::{
    ExecutionResult, Float, Handle, NumberError, ObjectType, PrimitiveContext,
    Tagged, Value, primitives::bool_object,
};

type Float2Op = fn(
    ctx: &mut PrimitiveContext,
    a: Handle<Float>,
    b: Handle<Float>,
) -> Result<Tagged<Float>, NumberError>;

fn float_binop(
    ctx: &mut PrimitiveContext<'_, '_>,
    op: Float2Op,
) -> ExecutionResult {
    // SAFETY: this is safe
    let a = unsafe { ctx.receiver.cast::<Float>() };
    // SAFETY: this is safe
    let b = unsafe { ctx.inputs[0].cast::<Float>() };
    match op(ctx, a, b) {
        Ok(res) => {
            ctx.outputs[0] =
                // SAFETY: this is safe
                unsafe { res.promote_to_handle().as_value_handle() }
        }
        Err(err) => return ExecutionResult::NumberError(err),
    }
    ExecutionResult::Normal
}

type Float1Op = fn(
    ctx: &mut PrimitiveContext,
    a: Handle<Float>,
) -> Result<Tagged<Float>, NumberError>;

fn float_op(
    ctx: &mut PrimitiveContext<'_, '_>,
    op: Float1Op,
) -> ExecutionResult {
    // SAFETY: this is safe
    let a = unsafe { ctx.receiver.cast::<Float>() };
    match op(ctx, a) {
        Ok(res) => {
            ctx.outputs[0] =
                // SAFETY: this is safe
                unsafe { res.promote_to_handle().as_value_handle() }
        }
        Err(err) => return ExecutionResult::NumberError(err),
    }
    ExecutionResult::Normal
}

type Float2LogicOp = fn(
    ctx: &mut PrimitiveContext,
    a: Handle<Float>,
    b: Handle<Float>,
) -> Result<bool, NumberError>;

fn float_logic_binop(
    ctx: &mut PrimitiveContext,
    op: Float2LogicOp,
) -> ExecutionResult {
    // SAFETY: this is safe
    let a = unsafe { ctx.receiver.cast::<Float>() };
    // SAFETY: this is safe
    let b = unsafe { ctx.inputs[0].cast::<Float>() };
    match op(ctx, a, b) {
        Ok(res) => ctx.outputs[0] = bool_object(ctx, res),
        Err(err) => return ExecutionResult::NumberError(err),
    }
    ExecutionResult::Normal
}

fn values(a: Handle<Float>, b: Handle<Float>) -> (f64, f64) {
    (a.value, b.value)
}

pub fn float_add(ctx: &mut PrimitiveContext) -> ExecutionResult {
    float_binop(ctx, |ctx, a, b| {
        let (a, b) = values(a, b);
        let res = a + b;
        let res = ctx.heap.allocate_float(res);
        Ok(res)
    })
}

pub fn float_sub(ctx: &mut PrimitiveContext) -> ExecutionResult {
    float_binop(ctx, |ctx, a, b| {
        let (a, b) = values(a, b);
        let res = a - b;
        let res = ctx.heap.allocate_float(res);
        Ok(res)
    })
}

pub fn float_mul(ctx: &mut PrimitiveContext) -> ExecutionResult {
    float_binop(ctx, |ctx, a, b| {
        let (a, b) = values(a, b);
        let res = a * b;
        let res = ctx.heap.allocate_float(res);
        Ok(res)
    })
}

pub fn float_div(ctx: &mut PrimitiveContext) -> ExecutionResult {
    float_binop(ctx, |ctx, a, b| {
        let (a, b) = values(a, b);
        let res = a / b;
        let res = ctx.heap.allocate_float(res);
        Ok(res)
    })
}

pub fn float_mod(ctx: &mut PrimitiveContext) -> ExecutionResult {
    float_binop(ctx, |ctx, a, b| {
        let (a, b) = values(a, b);
        let res = a % b;
        let res = ctx.heap.allocate_float(res);
        Ok(res)
    })
}

pub fn float_pow(ctx: &mut PrimitiveContext) -> ExecutionResult {
    float_binop(ctx, |ctx, a, b| {
        let (a, b) = values(a, b);
        let res = b.powf(a);
        let res = ctx.heap.allocate_float(res);
        Ok(res)
    })
}

pub fn float_exp(ctx: &mut PrimitiveContext) -> ExecutionResult {
    float_op(ctx, |ctx, a| {
        let a = a.value;
        let res = a.exp();
        let res = ctx.heap.allocate_float(res);
        Ok(res)
    })
}

pub fn float_sqrt(ctx: &mut PrimitiveContext) -> ExecutionResult {
    float_op(ctx, |ctx, a| {
        let a = a.value;
        let res = a.sqrt();
        let res = ctx.heap.allocate_float(res);
        Ok(res)
    })
}

pub fn float_exp2(ctx: &mut PrimitiveContext) -> ExecutionResult {
    float_op(ctx, |ctx, a| {
        let a = a.value;
        let res = a.exp2();
        let res = ctx.heap.allocate_float(res);
        Ok(res)
    })
}

pub fn float_sin(ctx: &mut PrimitiveContext) -> ExecutionResult {
    float_op(ctx, |ctx, a| {
        let a = a.value;
        let res = a.sin();
        let res = ctx.heap.allocate_float(res);
        Ok(res)
    })
}

pub fn float_cos(ctx: &mut PrimitiveContext) -> ExecutionResult {
    float_op(ctx, |ctx, a| {
        let a = a.value;
        let res = a.cos();
        let res = ctx.heap.allocate_float(res);
        Ok(res)
    })
}

pub fn float_tan(ctx: &mut PrimitiveContext) -> ExecutionResult {
    float_op(ctx, |ctx, a| {
        let a = a.value;
        let res = a.cos();
        let res = ctx.heap.allocate_float(res);
        Ok(res)
    })
}

pub fn float_asin(ctx: &mut PrimitiveContext) -> ExecutionResult {
    float_op(ctx, |ctx, a| {
        let a = a.value;
        let res = a.asin();
        let res = ctx.heap.allocate_float(res);
        Ok(res)
    })
}

pub fn float_acos(ctx: &mut PrimitiveContext) -> ExecutionResult {
    float_op(ctx, |ctx, a| {
        let a = a.value;
        let res = a.acos();
        let res = ctx.heap.allocate_float(res);
        Ok(res)
    })
}

pub fn float_atan(ctx: &mut PrimitiveContext) -> ExecutionResult {
    float_op(ctx, |ctx, a| {
        let a = a.value;
        let res = a.atan();
        let res = ctx.heap.allocate_float(res);
        Ok(res)
    })
}

pub fn float_neg(ctx: &mut PrimitiveContext) -> ExecutionResult {
    float_op(ctx, |ctx, a| {
        let a = a.value;
        let res = -a;
        let res = ctx.heap.allocate_float(res);
        Ok(res)
    })
}

pub fn float_eq(ctx: &mut PrimitiveContext) -> ExecutionResult {
    float_logic_binop(ctx, |_, a, b| {
        let (a, b) = values(a, b);
        let res = a == b;
        Ok(res)
    })
}

pub fn float_neq(ctx: &mut PrimitiveContext) -> ExecutionResult {
    float_logic_binop(ctx, |_, a, b| {
        let (a, b) = values(a, b);
        let res = a != b;
        Ok(res)
    })
}

pub fn float_gt(ctx: &mut PrimitiveContext) -> ExecutionResult {
    float_logic_binop(ctx, |_, a, b| {
        let (a, b) = values(a, b);
        let res = a > b;
        Ok(res)
    })
}

pub fn float_lt(ctx: &mut PrimitiveContext) -> ExecutionResult {
    float_logic_binop(ctx, |_, a, b| {
        let (a, b) = values(a, b);
        let res = a < b;
        Ok(res)
    })
}

pub fn float_geq(ctx: &mut PrimitiveContext) -> ExecutionResult {
    float_logic_binop(ctx, |_, a, b| {
        let (a, b) = values(a, b);
        let res = a >= b;
        Ok(res)
    })
}

pub fn float_leq(ctx: &mut PrimitiveContext) -> ExecutionResult {
    float_logic_binop(ctx, |_, a, b| {
        let (a, b) = values(a, b);
        let res = a <= b;
        Ok(res)
    })
}

fn is_float_object(obj: Handle<Value>) -> bool {
    if obj.is_fixnum() {
        return false;
    }
    // SAFETY: checked
    if let Some(ty) = unsafe { obj.as_heap_value_handle().header.object_type() }
    {
        return ty == ObjectType::Float;
    }
    false
}

pub fn is_float(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let res = is_float_object(ctx.receiver);
    ctx.outputs[0] = bool_object(ctx, res);
    ExecutionResult::Normal
}

pub fn is_2float(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let res1 = is_float_object(ctx.receiver);
    let res2 = is_float_object(ctx.inputs[0]);
    ctx.outputs[0] = bool_object(ctx, res1 && res2);
    ExecutionResult::Normal
}

pub fn float_to_utf8_bytes(ctx: &mut PrimitiveContext) -> ExecutionResult {
    // SAFETY: receiver must be valid float
    let value = unsafe { ctx.receiver.cast::<Float>() };
    let string = value.value.to_string();
    let ba = ctx.heap.allocate_bytearray_data(string.as_bytes());
    // SAFETY: no gc here
    ctx.outputs[0] = unsafe { ba.promote_to_handle().cast() };
    ExecutionResult::Normal
}

pub fn parent(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let p = ctx.vm.specials().float_traits;
    ctx.outputs[0] = p.into();
    ExecutionResult::Normal
}
