use std::cmp::Ordering;

use object::{Header, ObjectType, Ratio, Value};

use crate::alloc::alloc_ratio;
use crate::interpreter::{with_roots, InterpreterState, RuntimeError};
use crate::primitives::bignum::{
    add_big, alloc_bignum_value, bignum_value_to_value, cmp_big_value,
    div_mod_big, from_value as big_from_value, gcd_mag, mul_big, sub_big,
    BigNumValue,
};
use crate::primitives::string::alloc_vm_string;
use crate::primitives::{bool_value, expect_ratio};
use crate::VM;

fn gcd_u128(mut a: u128, mut b: u128) -> u128 {
    while b != 0 {
        let r = a % b;
        a = b;
        b = r;
    }
    a
}

fn is_fixnum(value: Value) -> Option<i64> {
    if value.is_fixnum() {
        Some(unsafe { value.to_i64() })
    } else {
        None
    }
}

fn denom_is_one(value: Value) -> Result<bool, RuntimeError> {
    if let Some(v) = is_fixnum(value) {
        return Ok(v == 1);
    }
    let ptr = crate::primitives::expect_bignum(value)?;
    let b = unsafe { &*ptr };
    Ok(b.sign == 1 && b.len() == 1 && b.limbs()[0] == 1)
}

fn ratio_parts(
    ratio: &Ratio,
) -> Result<(BigNumValue, BigNumValue), RuntimeError> {
    let numer = big_from_value(ratio.numerator)?;
    let denom = big_from_value(ratio.denominator)?;
    Ok((numer, denom))
}

fn to_f64(value: Value) -> Result<f64, RuntimeError> {
    if let Some(v) = is_fixnum(value) {
        return Ok(v as f64);
    }
    let ptr = crate::primitives::expect_bignum(value)?;
    let b = unsafe { &*ptr };
    let mut value = 0.0f64;
    for &limb in b.limbs().iter().rev() {
        value = value * 18446744073709551616.0 + (limb as f64);
        if !value.is_finite() {
            return Err(RuntimeError::Unimplemented {
                message: "bignum out of float range",
            });
        }
    }
    if b.sign < 0 {
        value = -value;
    }
    Ok(value)
}

fn make_ratio_from_bigvalues(
    vm: &mut VM,
    state: &mut InterpreterState,
    mut numer: BigNumValue,
    mut denom: BigNumValue,
    allow_demote: bool,
) -> Result<Value, RuntimeError> {
    if denom.sign == 0 {
        return Err(RuntimeError::Unimplemented {
            message: "division by zero",
        });
    }
    if numer.sign == 0 {
        if allow_demote {
            return Ok(Value::from_i64(0));
        }
        let mut scratch = Vec::new();
        let one = Value::from_i64(1);
        scratch.push(one);
        let ratio =
            with_roots(vm, state, &mut scratch, |proxy, roots| unsafe {
                alloc_ratio(proxy, roots, Value::from_i64(0), one).value()
            });
        return Ok(ratio);
    }

    if denom.sign < 0 {
        denom.sign = -denom.sign;
        numer.sign = -numer.sign;
    }

    let gcd = gcd_mag(&numer.limbs, &denom.limbs);
    if !gcd.is_empty() {
        let gcd_val = BigNumValue {
            sign: 1,
            limbs: gcd,
        };
        let (n_div, n_rem) = div_mod_big(&numer, &gcd_val)?;
        let (d_div, d_rem) = div_mod_big(&denom, &gcd_val)?;
        if n_rem.sign != 0 || d_rem.sign != 0 {
            return Err(RuntimeError::Unimplemented {
                message: "ratio normalization failed",
            });
        }
        numer = n_div;
        denom = d_div;
    }

    if allow_demote {
        if denom.sign == 1 && denom.limbs.len() == 1 && denom.limbs[0] == 1 {
            let mut scratch = Vec::new();
            return bignum_value_to_value(
                vm,
                state,
                &numer,
                &mut scratch,
                true,
            );
        }
    }

    let mut scratch = Vec::new();
    let numer_val =
        bignum_value_to_value(vm, state, &numer, &mut scratch, true)?;
    scratch.push(numer_val);
    let denom_val =
        bignum_value_to_value(vm, state, &denom, &mut scratch, true)?;
    scratch.push(denom_val);
    let ratio = with_roots(vm, state, &mut scratch, |proxy, roots| unsafe {
        alloc_ratio(proxy, roots, numer_val, denom_val).value()
    });
    Ok(ratio)
}

pub fn make_ratio(
    vm: &mut VM,
    state: &mut InterpreterState,
    numerator: Value,
    denominator: Value,
    allow_demote: bool,
) -> Result<Value, RuntimeError> {
    if let (Some(numer), Some(denom)) =
        (is_fixnum(numerator), is_fixnum(denominator))
    {
        if denom == 0 {
            return Err(RuntimeError::Unimplemented {
                message: "division by zero",
            });
        }
        if numer == 0 {
            if allow_demote {
                return Ok(Value::from_i64(0));
            }
            let mut scratch = Vec::new();
            let one = Value::from_i64(1);
            scratch.push(one);
            let ratio =
                with_roots(vm, state, &mut scratch, |proxy, roots| unsafe {
                    alloc_ratio(proxy, roots, Value::from_i64(0), one).value()
                });
            return Ok(ratio);
        }
        let mut n = numer as i128;
        let mut d = denom as i128;
        if d < 0 {
            n = -n;
            d = -d;
        }
        let gcd = gcd_u128(n.unsigned_abs(), d.unsigned_abs()) as i128;
        n /= gcd;
        d /= gcd;
        if allow_demote && d == 1 {
            return Ok(Value::from_i64(n as i64));
        }
        let mut scratch = Vec::new();
        let ratio =
            with_roots(vm, state, &mut scratch, |proxy, roots| unsafe {
                alloc_ratio(
                    proxy,
                    roots,
                    Value::from_i64(n as i64),
                    Value::from_i64(d as i64),
                )
                .value()
            });
        return Ok(ratio);
    }

    let numer = big_from_value(numerator)?;
    let denom = big_from_value(denominator)?;
    make_ratio_from_bigvalues(vm, state, numer, denom, allow_demote)
}

pub fn ratio_add(
    vm: &mut VM,
    state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let rhs = args.get(0).copied().ok_or(RuntimeError::TypeError {
        expected: "ratio",
        got: Value::from_i64(0),
    })?;
    let a = unsafe { &*expect_ratio(receiver)? };
    let b = unsafe { &*expect_ratio(rhs)? };
    let (n1, d1) = ratio_parts(a)?;
    let (n2, d2) = ratio_parts(b)?;
    let n = add_big(&mul_big(&n1, &d2), &mul_big(&n2, &d1));
    let d = mul_big(&d1, &d2);
    make_ratio_from_bigvalues(vm, state, n, d, true)
}

pub fn ratio_sub(
    vm: &mut VM,
    state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let rhs = args.get(0).copied().ok_or(RuntimeError::TypeError {
        expected: "ratio",
        got: Value::from_i64(0),
    })?;
    let a = unsafe { &*expect_ratio(receiver)? };
    let b = unsafe { &*expect_ratio(rhs)? };
    let (n1, d1) = ratio_parts(a)?;
    let (n2, d2) = ratio_parts(b)?;
    let n = sub_big(&mul_big(&n1, &d2), &mul_big(&n2, &d1));
    let d = mul_big(&d1, &d2);
    make_ratio_from_bigvalues(vm, state, n, d, true)
}

pub fn ratio_mul(
    vm: &mut VM,
    state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let rhs = args.get(0).copied().ok_or(RuntimeError::TypeError {
        expected: "ratio",
        got: Value::from_i64(0),
    })?;
    let a = unsafe { &*expect_ratio(receiver)? };
    let b = unsafe { &*expect_ratio(rhs)? };
    let (n1, d1) = ratio_parts(a)?;
    let (n2, d2) = ratio_parts(b)?;
    let n = mul_big(&n1, &n2);
    let d = mul_big(&d1, &d2);
    make_ratio_from_bigvalues(vm, state, n, d, true)
}

pub fn ratio_div(
    vm: &mut VM,
    state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let rhs = args.get(0).copied().ok_or(RuntimeError::TypeError {
        expected: "ratio",
        got: Value::from_i64(0),
    })?;
    let a = unsafe { &*expect_ratio(receiver)? };
    let b = unsafe { &*expect_ratio(rhs)? };
    let (n1, d1) = ratio_parts(a)?;
    let (n2, d2) = ratio_parts(b)?;
    if n2.sign == 0 {
        return Err(RuntimeError::Unimplemented {
            message: "division by zero",
        });
    }
    let n = mul_big(&n1, &d2);
    let d = mul_big(&d1, &n2);
    make_ratio_from_bigvalues(vm, state, n, d, true)
}

pub fn ratio_neg(
    vm: &mut VM,
    state: &mut InterpreterState,
    receiver: Value,
    _args: &[Value],
) -> Result<Value, RuntimeError> {
    let r = unsafe { &*expect_ratio(receiver)? };
    let (mut n, d) = ratio_parts(r)?;
    n.sign = -n.sign;
    make_ratio_from_bigvalues(vm, state, n, d, true)
}

pub fn ratio_numerator(
    _vm: &mut VM,
    _state: &mut InterpreterState,
    receiver: Value,
    _args: &[Value],
) -> Result<Value, RuntimeError> {
    let r = unsafe { &*expect_ratio(receiver)? };
    Ok(r.numerator)
}

pub fn ratio_denominator(
    _vm: &mut VM,
    _state: &mut InterpreterState,
    receiver: Value,
    _args: &[Value],
) -> Result<Value, RuntimeError> {
    let r = unsafe { &*expect_ratio(receiver)? };
    Ok(r.denominator)
}

pub fn ratio_to_fixnum(
    _vm: &mut VM,
    _state: &mut InterpreterState,
    receiver: Value,
    _args: &[Value],
) -> Result<Value, RuntimeError> {
    let r = unsafe { &*expect_ratio(receiver)? };
    if denom_is_one(r.denominator)? {
        if let Some(v) = is_fixnum(r.numerator) {
            return Ok(Value::from_i64(v));
        }
    }
    Err(RuntimeError::Unimplemented {
        message: "ratio not integral",
    })
}

pub fn ratio_to_bignum(
    vm: &mut VM,
    state: &mut InterpreterState,
    receiver: Value,
    _args: &[Value],
) -> Result<Value, RuntimeError> {
    let r = unsafe { &*expect_ratio(receiver)? };
    if !denom_is_one(r.denominator)? {
        return Err(RuntimeError::Unimplemented {
            message: "ratio not integral",
        });
    }
    if r.numerator.is_ref() {
        let header: &Header = unsafe { r.numerator.as_ref() };
        if header.object_type() == ObjectType::BigNum {
            return Ok(r.numerator);
        }
    }
    if r.numerator.is_fixnum() {
        let v = unsafe { r.numerator.to_i64() } as i128;
        let mut scratch = vec![receiver, r.numerator];
        let bn = with_roots(vm, state, &mut scratch, |proxy, roots| unsafe {
            crate::alloc::alloc_bignum_from_i128(proxy, roots, v).value()
        });
        return Ok(bn);
    }
    let mut scratch = vec![receiver, r.numerator];
    let val = big_from_value(r.numerator)?;
    alloc_bignum_value(vm, state, &val, &mut scratch)
}

pub fn ratio_to_float(
    vm: &mut VM,
    state: &mut InterpreterState,
    receiver: Value,
    _args: &[Value],
) -> Result<Value, RuntimeError> {
    let r = unsafe { &*expect_ratio(receiver)? };
    let numer = to_f64(r.numerator)?;
    let denom = to_f64(r.denominator)?;
    if denom == 0.0 {
        return Err(RuntimeError::Unimplemented {
            message: "division by zero",
        });
    }
    let value = numer / denom;
    let mut scratch = vec![receiver];
    let float = with_roots(vm, state, &mut scratch, |proxy, roots| unsafe {
        crate::alloc::alloc_float(proxy, roots, value).value()
    });
    Ok(float)
}

pub fn ratio_to_string(
    vm: &mut VM,
    state: &mut InterpreterState,
    receiver: Value,
    _args: &[Value],
) -> Result<Value, RuntimeError> {
    let r = unsafe { &*expect_ratio(receiver)? };
    let numer = value_to_string(r.numerator)?;
    let denom = value_to_string(r.denominator)?;
    let text = format!("{}/{}", numer, denom);
    alloc_vm_string(vm, state, text.as_bytes())
}

pub fn ratio_eq(
    vm: &mut VM,
    _state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let rhs = args.get(0).copied().ok_or(RuntimeError::TypeError {
        expected: "ratio",
        got: Value::from_i64(0),
    })?;
    let a = unsafe { &*expect_ratio(receiver)? };
    let b = unsafe { &*expect_ratio(rhs)? };
    let (n1, d1) = ratio_parts(a)?;
    let (n2, d2) = ratio_parts(b)?;
    let left = mul_big(&n1, &d2);
    let right = mul_big(&n2, &d1);
    Ok(bool_value(
        vm,
        cmp_big_value(&left, &right) == Ordering::Equal,
    ))
}

pub fn ratio_ne(
    vm: &mut VM,
    _state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let rhs = args.get(0).copied().ok_or(RuntimeError::TypeError {
        expected: "ratio",
        got: Value::from_i64(0),
    })?;
    let a = unsafe { &*expect_ratio(receiver)? };
    let b = unsafe { &*expect_ratio(rhs)? };
    let (n1, d1) = ratio_parts(a)?;
    let (n2, d2) = ratio_parts(b)?;
    let left = mul_big(&n1, &d2);
    let right = mul_big(&n2, &d1);
    Ok(bool_value(
        vm,
        cmp_big_value(&left, &right) != Ordering::Equal,
    ))
}

pub fn ratio_lt(
    vm: &mut VM,
    _state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let rhs = args.get(0).copied().ok_or(RuntimeError::TypeError {
        expected: "ratio",
        got: Value::from_i64(0),
    })?;
    let a = unsafe { &*expect_ratio(receiver)? };
    let b = unsafe { &*expect_ratio(rhs)? };
    let (n1, d1) = ratio_parts(a)?;
    let (n2, d2) = ratio_parts(b)?;
    let left = mul_big(&n1, &d2);
    let right = mul_big(&n2, &d1);
    Ok(bool_value(
        vm,
        cmp_big_value(&left, &right) == Ordering::Less,
    ))
}

pub fn ratio_le(
    vm: &mut VM,
    _state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let rhs = args.get(0).copied().ok_or(RuntimeError::TypeError {
        expected: "ratio",
        got: Value::from_i64(0),
    })?;
    let a = unsafe { &*expect_ratio(receiver)? };
    let b = unsafe { &*expect_ratio(rhs)? };
    let (n1, d1) = ratio_parts(a)?;
    let (n2, d2) = ratio_parts(b)?;
    let left = mul_big(&n1, &d2);
    let right = mul_big(&n2, &d1);
    let cmp = cmp_big_value(&left, &right);
    Ok(bool_value(
        vm,
        cmp == Ordering::Less || cmp == Ordering::Equal,
    ))
}

pub fn ratio_gt(
    vm: &mut VM,
    _state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let rhs = args.get(0).copied().ok_or(RuntimeError::TypeError {
        expected: "ratio",
        got: Value::from_i64(0),
    })?;
    let a = unsafe { &*expect_ratio(receiver)? };
    let b = unsafe { &*expect_ratio(rhs)? };
    let (n1, d1) = ratio_parts(a)?;
    let (n2, d2) = ratio_parts(b)?;
    let left = mul_big(&n1, &d2);
    let right = mul_big(&n2, &d1);
    Ok(bool_value(
        vm,
        cmp_big_value(&left, &right) == Ordering::Greater,
    ))
}

pub fn ratio_ge(
    vm: &mut VM,
    _state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let rhs = args.get(0).copied().ok_or(RuntimeError::TypeError {
        expected: "ratio",
        got: Value::from_i64(0),
    })?;
    let a = unsafe { &*expect_ratio(receiver)? };
    let b = unsafe { &*expect_ratio(rhs)? };
    let (n1, d1) = ratio_parts(a)?;
    let (n2, d2) = ratio_parts(b)?;
    let left = mul_big(&n1, &d2);
    let right = mul_big(&n2, &d1);
    let cmp = cmp_big_value(&left, &right);
    Ok(bool_value(
        vm,
        cmp == Ordering::Greater || cmp == Ordering::Equal,
    ))
}

fn value_to_string(value: Value) -> Result<String, RuntimeError> {
    if value.is_fixnum() {
        let v = unsafe { value.to_i64() };
        return Ok(v.to_string());
    }
    let header: &Header = unsafe { value.as_ref() };
    if header.object_type() == ObjectType::BigNum {
        let b = unsafe { &*(value.ref_bits() as *const object::BigNum) };
        let text = crate::primitives::bignum::big_to_string(
            &crate::primitives::bignum::from_bignum(b),
        );
        return Ok(text);
    }
    Err(RuntimeError::TypeError {
        expected: "numeric",
        got: value,
    })
}
