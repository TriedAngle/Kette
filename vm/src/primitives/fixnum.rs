use object::BigNum;
use object::Value;

use crate::alloc::{alloc_bignum_from_i128, alloc_float};
use crate::interpreter::{with_roots, InterpreterState, RuntimeError};
use crate::primitives::ratio;
use crate::primitives::string::alloc_vm_string;
use crate::primitives::{bool_value, expect_fixnum};
use crate::VM;

fn fits_fixnum(value: i128) -> bool {
    value >= -(BigNum::FIXNUM_MAX as i128) - 1
        && value <= BigNum::FIXNUM_MAX as i128
}

fn value_from_i128(
    vm: &mut VM,
    state: &mut InterpreterState,
    value: i128,
    scratch: &mut Vec<Value>,
) -> Result<Value, RuntimeError> {
    if fits_fixnum(value) {
        Ok(Value::from_i64(value as i64))
    } else {
        let bn = with_roots(vm, state, scratch, |proxy, roots| unsafe {
            alloc_bignum_from_i128(proxy, roots, value).value()
        });
        Ok(bn)
    }
}

pub fn fixnum_add(
    vm: &mut VM,
    state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let rhs = args.first().copied().ok_or(RuntimeError::TypeError {
        expected: "fixnum",
        got: Value::from_i64(0),
    })?;
    let a = expect_fixnum(receiver)?;
    let b = expect_fixnum(rhs)?;
    let sum = (a as i128) + (b as i128);
    let mut scratch = vec![receiver, rhs];
    value_from_i128(vm, state, sum, &mut scratch)
}

pub fn fixnum_sub(
    vm: &mut VM,
    state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let rhs = args.first().copied().ok_or(RuntimeError::TypeError {
        expected: "fixnum",
        got: Value::from_i64(0),
    })?;
    let a = expect_fixnum(receiver)?;
    let b = expect_fixnum(rhs)?;
    let diff = (a as i128) - (b as i128);
    let mut scratch = vec![receiver, rhs];
    value_from_i128(vm, state, diff, &mut scratch)
}

pub fn fixnum_mul(
    vm: &mut VM,
    state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let rhs = args.first().copied().ok_or(RuntimeError::TypeError {
        expected: "fixnum",
        got: Value::from_i64(0),
    })?;
    let a = expect_fixnum(receiver)?;
    let b = expect_fixnum(rhs)?;
    let prod = (a as i128) * (b as i128);
    let mut scratch = vec![receiver, rhs];
    value_from_i128(vm, state, prod, &mut scratch)
}

pub fn fixnum_div(
    vm: &mut VM,
    state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let rhs = args.first().copied().ok_or(RuntimeError::TypeError {
        expected: "fixnum",
        got: Value::from_i64(0),
    })?;
    let a = expect_fixnum(receiver)?;
    let b = expect_fixnum(rhs)?;
    if b == 0 {
        return Err(RuntimeError::Unimplemented {
            message: "division by zero",
        });
    }
    if a % b == 0 {
        let quot = (a as i128) / (b as i128);
        let mut scratch = vec![receiver, rhs];
        return value_from_i128(vm, state, quot, &mut scratch);
    }

    ratio::make_ratio(vm, state, Value::from_i64(a), Value::from_i64(b), true)
}

pub fn fixnum_mod(
    _vm: &mut VM,
    _state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let rhs = args.first().copied().ok_or(RuntimeError::TypeError {
        expected: "fixnum",
        got: Value::from_i64(0),
    })?;
    let a = expect_fixnum(receiver)?;
    let b = expect_fixnum(rhs)?;
    if b == 0 {
        return Err(RuntimeError::Unimplemented {
            message: "division by zero",
        });
    }
    Ok(Value::from_i64(a % b))
}

pub fn fixnum_neg(
    vm: &mut VM,
    state: &mut InterpreterState,
    receiver: Value,
    _args: &[Value],
) -> Result<Value, RuntimeError> {
    let a = expect_fixnum(receiver)?;
    let neg = -(a as i128);
    let mut scratch = vec![receiver];
    value_from_i128(vm, state, neg, &mut scratch)
}

pub fn fixnum_to_bignum(
    vm: &mut VM,
    state: &mut InterpreterState,
    receiver: Value,
    _args: &[Value],
) -> Result<Value, RuntimeError> {
    let value = expect_fixnum(receiver)? as i128;
    let mut scratch = vec![receiver];
    let bn = with_roots(vm, state, &mut scratch, |proxy, roots| unsafe {
        alloc_bignum_from_i128(proxy, roots, value).value()
    });
    Ok(bn)
}

pub fn fixnum_to_ratio(
    vm: &mut VM,
    state: &mut InterpreterState,
    receiver: Value,
    _args: &[Value],
) -> Result<Value, RuntimeError> {
    let value = expect_fixnum(receiver)?;
    ratio::make_ratio(
        vm,
        state,
        Value::from_i64(value),
        Value::from_i64(1),
        false,
    )
}

pub fn fixnum_to_float(
    vm: &mut VM,
    state: &mut InterpreterState,
    receiver: Value,
    _args: &[Value],
) -> Result<Value, RuntimeError> {
    let value = expect_fixnum(receiver)? as f64;
    let mut scratch = vec![receiver];
    let float = with_roots(vm, state, &mut scratch, |proxy, roots| unsafe {
        alloc_float(proxy, roots, value).value()
    });
    Ok(float)
}

pub fn fixnum_to_string(
    vm: &mut VM,
    state: &mut InterpreterState,
    receiver: Value,
    _args: &[Value],
) -> Result<Value, RuntimeError> {
    let value = expect_fixnum(receiver)?;
    alloc_vm_string(vm, state, value.to_string().as_bytes())
}

pub fn fixnum_to_string_radix(
    vm: &mut VM,
    state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let radix_val = args.first().copied().ok_or(RuntimeError::TypeError {
        expected: "fixnum radix",
        got: Value::from_i64(0),
    })?;
    let radix = expect_fixnum(radix_val)? as u32;
    if !(2..=36).contains(&radix) {
        return Err(RuntimeError::Unimplemented {
            message: "radix out of range",
        });
    }
    let value = expect_fixnum(receiver)?;
    let text = if value < 0 {
        format!("-{}", to_radix((-value) as u64, radix))
    } else {
        to_radix(value as u64, radix)
    };
    alloc_vm_string(vm, state, text.as_bytes())
}

pub fn fixnum_eq(
    vm: &mut VM,
    _state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let rhs = args.first().copied().ok_or(RuntimeError::TypeError {
        expected: "fixnum",
        got: Value::from_i64(0),
    })?;
    let a = expect_fixnum(receiver)?;
    let b = expect_fixnum(rhs)?;
    Ok(bool_value(vm, a == b))
}

pub fn fixnum_ne(
    vm: &mut VM,
    _state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let rhs = args.first().copied().ok_or(RuntimeError::TypeError {
        expected: "fixnum",
        got: Value::from_i64(0),
    })?;
    let a = expect_fixnum(receiver)?;
    let b = expect_fixnum(rhs)?;
    Ok(bool_value(vm, a != b))
}

pub fn fixnum_lt(
    vm: &mut VM,
    _state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let rhs = args.first().copied().ok_or(RuntimeError::TypeError {
        expected: "fixnum",
        got: Value::from_i64(0),
    })?;
    let a = expect_fixnum(receiver)?;
    let b = expect_fixnum(rhs)?;
    Ok(bool_value(vm, a < b))
}

pub fn fixnum_le(
    vm: &mut VM,
    _state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let rhs = args.first().copied().ok_or(RuntimeError::TypeError {
        expected: "fixnum",
        got: Value::from_i64(0),
    })?;
    let a = expect_fixnum(receiver)?;
    let b = expect_fixnum(rhs)?;
    Ok(bool_value(vm, a <= b))
}

pub fn fixnum_gt(
    vm: &mut VM,
    _state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let rhs = args.first().copied().ok_or(RuntimeError::TypeError {
        expected: "fixnum",
        got: Value::from_i64(0),
    })?;
    let a = expect_fixnum(receiver)?;
    let b = expect_fixnum(rhs)?;
    Ok(bool_value(vm, a > b))
}

pub fn fixnum_ge(
    vm: &mut VM,
    _state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let rhs = args.first().copied().ok_or(RuntimeError::TypeError {
        expected: "fixnum",
        got: Value::from_i64(0),
    })?;
    let a = expect_fixnum(receiver)?;
    let b = expect_fixnum(rhs)?;
    Ok(bool_value(vm, a >= b))
}

fn to_radix(mut value: u64, radix: u32) -> String {
    if value == 0 {
        return "0".to_string();
    }
    let mut buf = Vec::new();
    let r = radix as u64;
    while value != 0 {
        let digit = (value % r) as u8;
        let ch = match digit {
            0..=9 => (b'0' + digit) as char,
            _ => (b'a' + (digit - 10)) as char,
        };
        buf.push(ch);
        value /= r;
    }
    buf.iter().rev().collect()
}
