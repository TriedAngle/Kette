use object::BigNum;
use object::Value;

use crate::alloc::{alloc_bignum_from_i128, alloc_float};
use crate::interpreter::{with_roots, InterpreterState, RuntimeError};
use crate::primitives::ratio;
use crate::primitives::{bool_value, expect_float};
use crate::VM;

fn float_to_i128(value: f64) -> Result<i128, RuntimeError> {
    if !value.is_finite() {
        return Err(RuntimeError::Unimplemented {
            message: "float must be finite",
        });
    }
    let truncated = value.trunc();
    if truncated != value {
        return Err(RuntimeError::Unimplemented {
            message: "float must be integral",
        });
    }
    if truncated < (i128::MIN as f64) || truncated > (i128::MAX as f64) {
        return Err(RuntimeError::Unimplemented {
            message: "float out of range",
        });
    }
    Ok(truncated as i128)
}

pub fn float_to_fixnum(
    _vm: &mut VM,
    _state: &mut InterpreterState,
    receiver: Value,
    _args: &[Value],
) -> Result<Value, RuntimeError> {
    let ptr = expect_float(receiver)?;
    let value = unsafe { (*ptr).value };
    let int = float_to_i128(value)?;
    if int < -(BigNum::FIXNUM_MAX as i128) - 1
        || int > BigNum::FIXNUM_MAX as i128
    {
        return Err(RuntimeError::Unimplemented {
            message: "float out of fixnum range",
        });
    }
    Ok(Value::from_i64(int as i64))
}

pub fn float_to_bignum(
    vm: &mut VM,
    state: &mut InterpreterState,
    receiver: Value,
    _args: &[Value],
) -> Result<Value, RuntimeError> {
    let ptr = expect_float(receiver)?;
    let value = unsafe { (*ptr).value };
    let int = float_to_i128(value)?;
    let mut scratch = vec![receiver];
    let bn = with_roots(vm, state, &mut scratch, |proxy, roots| unsafe {
        alloc_bignum_from_i128(proxy, roots, int).value()
    });
    Ok(bn)
}

pub fn float_to_ratio(
    vm: &mut VM,
    state: &mut InterpreterState,
    receiver: Value,
    _args: &[Value],
) -> Result<Value, RuntimeError> {
    let ptr = expect_float(receiver)?;
    let value = unsafe { (*ptr).value };
    let int = float_to_i128(value)?;
    ratio::make_ratio(
        vm,
        state,
        Value::from_i64(int as i64),
        Value::from_i64(1),
        false,
    )
}

pub fn float_to_string(
    vm: &mut VM,
    state: &mut InterpreterState,
    receiver: Value,
    _args: &[Value],
) -> Result<Value, RuntimeError> {
    let ptr = expect_float(receiver)?;
    let value = unsafe { (*ptr).value };
    let text = value.to_string();
    crate::primitives::string::alloc_vm_string(vm, state, text.as_bytes())
}

pub fn float_to_string_digits(
    vm: &mut VM,
    state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let digits_val = args.get(0).copied().ok_or(RuntimeError::TypeError {
        expected: "digits",
        got: Value::from_i64(0),
    })?;
    if !digits_val.is_fixnum() {
        return Err(RuntimeError::TypeError {
            expected: "digits",
            got: digits_val,
        });
    }
    let digits = unsafe { digits_val.to_i64() };
    if digits < 0 || digits > 50 {
        return Err(RuntimeError::Unimplemented {
            message: "digits out of range",
        });
    }
    let ptr = expect_float(receiver)?;
    let value = unsafe { (*ptr).value };
    let text = format!("{:.*}", digits as usize, value);
    crate::primitives::string::alloc_vm_string(vm, state, text.as_bytes())
}

pub fn float_eq(
    vm: &mut VM,
    _state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let rhs = args.get(0).copied().ok_or(RuntimeError::TypeError {
        expected: "float",
        got: Value::from_i64(0),
    })?;
    let a = unsafe { (*expect_float(receiver)?).value };
    let b = unsafe { (*expect_float(rhs)?).value };
    Ok(bool_value(vm, a == b))
}

pub fn float_ne(
    vm: &mut VM,
    _state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let rhs = args.get(0).copied().ok_or(RuntimeError::TypeError {
        expected: "float",
        got: Value::from_i64(0),
    })?;
    let a = unsafe { (*expect_float(receiver)?).value };
    let b = unsafe { (*expect_float(rhs)?).value };
    Ok(bool_value(vm, a != b))
}

pub fn float_lt(
    vm: &mut VM,
    _state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let rhs = args.get(0).copied().ok_or(RuntimeError::TypeError {
        expected: "float",
        got: Value::from_i64(0),
    })?;
    let a = unsafe { (*expect_float(receiver)?).value };
    let b = unsafe { (*expect_float(rhs)?).value };
    Ok(bool_value(vm, a < b))
}

pub fn float_le(
    vm: &mut VM,
    _state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let rhs = args.get(0).copied().ok_or(RuntimeError::TypeError {
        expected: "float",
        got: Value::from_i64(0),
    })?;
    let a = unsafe { (*expect_float(receiver)?).value };
    let b = unsafe { (*expect_float(rhs)?).value };
    Ok(bool_value(vm, a <= b))
}

pub fn float_gt(
    vm: &mut VM,
    _state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let rhs = args.get(0).copied().ok_or(RuntimeError::TypeError {
        expected: "float",
        got: Value::from_i64(0),
    })?;
    let a = unsafe { (*expect_float(receiver)?).value };
    let b = unsafe { (*expect_float(rhs)?).value };
    Ok(bool_value(vm, a > b))
}

pub fn float_ge(
    vm: &mut VM,
    _state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let rhs = args.get(0).copied().ok_or(RuntimeError::TypeError {
        expected: "float",
        got: Value::from_i64(0),
    })?;
    let a = unsafe { (*expect_float(receiver)?).value };
    let b = unsafe { (*expect_float(rhs)?).value };
    Ok(bool_value(vm, a >= b))
}

pub fn float_approx_eq(
    vm: &mut VM,
    _state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let rhs = args.get(0).copied().ok_or(RuntimeError::TypeError {
        expected: "float",
        got: Value::from_i64(0),
    })?;
    let eps_val = args.get(1).copied().ok_or(RuntimeError::TypeError {
        expected: "float epsilon",
        got: Value::from_i64(0),
    })?;
    let a = unsafe { (*expect_float(receiver)?).value };
    let b = unsafe { (*expect_float(rhs)?).value };
    let eps = unsafe { (*expect_float(eps_val)?).value };
    Ok(bool_value(vm, (a - b).abs() <= eps))
}

pub fn float_add(
    vm: &mut VM,
    state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let rhs = args.get(0).copied().ok_or(RuntimeError::TypeError {
        expected: "float",
        got: Value::from_i64(0),
    })?;
    let a = unsafe { (*expect_float(receiver)?).value };
    let b = unsafe { (*expect_float(rhs)?).value };
    let mut scratch = vec![receiver, rhs];
    let float = with_roots(vm, state, &mut scratch, |proxy, roots| unsafe {
        alloc_float(proxy, roots, a + b).value()
    });
    Ok(float)
}

pub fn float_sub(
    vm: &mut VM,
    state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let rhs = args.get(0).copied().ok_or(RuntimeError::TypeError {
        expected: "float",
        got: Value::from_i64(0),
    })?;
    let a = unsafe { (*expect_float(receiver)?).value };
    let b = unsafe { (*expect_float(rhs)?).value };
    let mut scratch = vec![receiver, rhs];
    let float = with_roots(vm, state, &mut scratch, |proxy, roots| unsafe {
        alloc_float(proxy, roots, a - b).value()
    });
    Ok(float)
}

pub fn float_mul(
    vm: &mut VM,
    state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let rhs = args.get(0).copied().ok_or(RuntimeError::TypeError {
        expected: "float",
        got: Value::from_i64(0),
    })?;
    let a = unsafe { (*expect_float(receiver)?).value };
    let b = unsafe { (*expect_float(rhs)?).value };
    let mut scratch = vec![receiver, rhs];
    let float = with_roots(vm, state, &mut scratch, |proxy, roots| unsafe {
        alloc_float(proxy, roots, a * b).value()
    });
    Ok(float)
}

pub fn float_div(
    vm: &mut VM,
    state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let rhs = args.get(0).copied().ok_or(RuntimeError::TypeError {
        expected: "float",
        got: Value::from_i64(0),
    })?;
    let a = unsafe { (*expect_float(receiver)?).value };
    let b = unsafe { (*expect_float(rhs)?).value };
    let mut scratch = vec![receiver, rhs];
    let float = with_roots(vm, state, &mut scratch, |proxy, roots| unsafe {
        alloc_float(proxy, roots, a / b).value()
    });
    Ok(float)
}

pub fn float_mod(
    vm: &mut VM,
    state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let rhs = args.get(0).copied().ok_or(RuntimeError::TypeError {
        expected: "float",
        got: Value::from_i64(0),
    })?;
    let a = unsafe { (*expect_float(receiver)?).value };
    let b = unsafe { (*expect_float(rhs)?).value };
    let mut scratch = vec![receiver, rhs];
    let float = with_roots(vm, state, &mut scratch, |proxy, roots| unsafe {
        alloc_float(proxy, roots, a % b).value()
    });
    Ok(float)
}

pub fn float_neg(
    vm: &mut VM,
    state: &mut InterpreterState,
    receiver: Value,
    _args: &[Value],
) -> Result<Value, RuntimeError> {
    let a = unsafe { (*expect_float(receiver)?).value };
    let mut scratch = vec![receiver];
    let float = with_roots(vm, state, &mut scratch, |proxy, roots| unsafe {
        alloc_float(proxy, roots, -a).value()
    });
    Ok(float)
}

pub fn float_sqrt(
    vm: &mut VM,
    state: &mut InterpreterState,
    receiver: Value,
    _args: &[Value],
) -> Result<Value, RuntimeError> {
    let a = unsafe { (*expect_float(receiver)?).value };
    let mut scratch = vec![receiver];
    let float = with_roots(vm, state, &mut scratch, |proxy, roots| unsafe {
        alloc_float(proxy, roots, a.sqrt()).value()
    });
    Ok(float)
}
