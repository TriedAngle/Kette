use std::cmp::Ordering;

use object::{BigNum, Value};

use crate::alloc::alloc_bignum_from_limbs;
use crate::interpreter::{with_roots, InterpreterState, RuntimeError};
use crate::primitives::bool_value;
use crate::primitives::expect_bignum;
use crate::primitives::ratio;
use crate::primitives::string::alloc_vm_string;
use crate::VM;

#[derive(Clone)]
pub struct BigNumValue {
    pub sign: i8,
    pub limbs: Vec<u64>,
}

impl BigNumValue {
    pub fn normalize(&mut self) {
        let len = normalize_len(&mut self.limbs);
        if len == 0 {
            self.sign = 0;
        }
    }
}

pub(crate) fn from_bignum(bn: &BigNum) -> BigNumValue {
    BigNumValue {
        sign: bn.sign,
        limbs: bn.limbs().to_vec(),
    }
}

pub(crate) fn from_fixnum(value: i64) -> BigNumValue {
    if value == 0 {
        return BigNumValue {
            sign: 0,
            limbs: Vec::new(),
        };
    }
    let sign = if value < 0 { -1 } else { 1 };
    let mut mag = value.unsigned_abs() as u128;
    let mut limbs = Vec::new();
    while mag != 0 {
        limbs.push((mag & u64::MAX as u128) as u64);
        mag >>= 64;
    }
    BigNumValue { sign, limbs }
}

pub(crate) fn from_value(value: Value) -> Result<BigNumValue, RuntimeError> {
    if value.is_fixnum() {
        let val = unsafe { value.to_i64() };
        return Ok(from_fixnum(val));
    }
    let ptr = expect_bignum(value)?;
    let bn = unsafe { &*ptr };
    Ok(from_bignum(bn))
}

fn normalize_len(limbs: &mut Vec<u64>) -> usize {
    let mut idx = limbs.len();
    while idx > 0 {
        if limbs[idx - 1] != 0 {
            break;
        }
        idx -= 1;
    }
    limbs.truncate(idx);
    idx
}

fn cmp_mag_slices(a: &[u64], b: &[u64]) -> Ordering {
    let mut a_len = a.len();
    let mut b_len = b.len();
    while a_len > 0 && a[a_len - 1] == 0 {
        a_len -= 1;
    }
    while b_len > 0 && b[b_len - 1] == 0 {
        b_len -= 1;
    }
    if a_len != b_len {
        return a_len.cmp(&b_len);
    }
    for i in (0..a_len).rev() {
        let ai = a[i];
        let bi = b[i];
        if ai != bi {
            return ai.cmp(&bi);
        }
    }
    Ordering::Equal
}

fn add_mag(a: &[u64], b: &[u64]) -> Vec<u64> {
    let max_len = a.len().max(b.len());
    let mut out = Vec::with_capacity(max_len + 1);
    let mut carry: u128 = 0;
    for i in 0..max_len {
        let av = if i < a.len() { a[i] } else { 0 };
        let bv = if i < b.len() { b[i] } else { 0 };
        let sum = (av as u128) + (bv as u128) + carry;
        out.push(sum as u64);
        carry = sum >> 64;
    }
    if carry != 0 {
        out.push(carry as u64);
    }
    out
}

fn sub_mag(a: &[u64], b: &[u64]) -> Vec<u64> {
    let mut out = Vec::with_capacity(a.len());
    let mut borrow = 0u64;
    for i in 0..a.len() {
        let av = a[i];
        let bv = if i < b.len() { b[i] } else { 0 };
        let (res1, overflow1) = av.overflowing_sub(bv);
        let (res2, overflow2) = res1.overflowing_sub(borrow);
        out.push(res2);
        borrow = (overflow1 as u64) | (overflow2 as u64);
    }
    normalize_len(&mut out);
    out
}

fn mul_mag(a: &[u64], b: &[u64]) -> Vec<u64> {
    if a.is_empty() || b.is_empty() {
        return Vec::new();
    }
    let mut out = vec![0u64; a.len() + b.len()];
    for (i, &a_limb) in a.iter().enumerate() {
        let mut carry = 0u128;
        let av = a_limb as u128;
        for (j, &b_limb) in b.iter().enumerate() {
            let idx = i + j;
            let acc = out[idx] as u128 + av * (b_limb as u128) + carry;
            out[idx] = acc as u64;
            carry = acc >> 64;
        }
        let idx = i + b.len();
        if idx < out.len() {
            let acc = out[idx] as u128 + carry;
            out[idx] = acc as u64;
            let mut k = idx + 1;
            let mut carry2 = acc >> 64;
            while carry2 != 0 && k < out.len() {
                let acc2 = out[k] as u128 + carry2;
                out[k] = acc2 as u64;
                carry2 = acc2 >> 64;
                k += 1;
            }
        }
    }
    normalize_len(&mut out);
    out
}

fn shl_bits(limbs: &[u64], shift: u32) -> Vec<u64> {
    if shift == 0 {
        return limbs.to_vec();
    }
    let mut out = Vec::with_capacity(limbs.len() + 1);
    let mut carry = 0u64;
    for &limb in limbs {
        let next = (limb << shift) | carry;
        out.push(next);
        carry = limb >> (64 - shift);
    }
    if carry != 0 {
        out.push(carry);
    }
    out
}

fn shr_bits(limbs: &[u64], shift: u32) -> Vec<u64> {
    if shift == 0 {
        return limbs.to_vec();
    }
    let mut out = vec![0u64; limbs.len()];
    let mut carry = 0u64;
    for i in (0..limbs.len()).rev() {
        let limb = limbs[i];
        out[i] = (limb >> shift) | carry;
        carry = limb << (64 - shift);
    }
    out
}

fn div_mod_mag_single(a: &[u64], divisor: u64) -> (Vec<u64>, Vec<u64>) {
    let mut q = vec![0u64; a.len()];
    let mut rem = 0u128;
    for i in (0..a.len()).rev() {
        let num = (rem << 64) | (a[i] as u128);
        let qdigit = num / (divisor as u128);
        rem = num % (divisor as u128);
        q[i] = qdigit as u64;
    }
    let q_len = normalize_len(&mut q);
    q.truncate(q_len);
    if rem == 0 {
        return (q, Vec::new());
    }
    (q, vec![rem as u64])
}

fn div_mod_mag(a: &[u64], b: &[u64]) -> (Vec<u64>, Vec<u64>) {
    let mut a_len = a.len();
    let mut b_len = b.len();
    while a_len > 0 && a[a_len - 1] == 0 {
        a_len -= 1;
    }
    while b_len > 0 && b[b_len - 1] == 0 {
        b_len -= 1;
    }
    if a_len == 0 {
        return (Vec::new(), Vec::new());
    }
    if b_len == 1 {
        return div_mod_mag_single(&a[..a_len], b[0]);
    }
    if cmp_mag_slices(&a[..a_len], &b[..b_len]) == Ordering::Less {
        return (Vec::new(), a[..a_len].to_vec());
    }

    let n = b_len;
    let m = a_len - n;
    let shift = b[b_len - 1].leading_zeros();
    let v = shl_bits(&b[..b_len], shift);
    let mut u = shl_bits(&a[..a_len], shift);
    if u.len() == a_len {
        u.push(0);
    }

    let base: u128 = 1u128 << 64;
    let mut q = vec![0u64; m + 1];
    for j in (0..=m).rev() {
        let u_jn = u[j + n] as u128;
        let u_jn1 = u[j + n - 1] as u128;
        let numerator = (u_jn << 64) | u_jn1;
        let mut qhat = numerator / (v[n - 1] as u128);
        let mut rhat = numerator % (v[n - 1] as u128);
        if qhat == base {
            qhat = base - 1;
            rhat += v[n - 1] as u128;
        }
        if n > 1 {
            let v_n2 = v[n - 2] as u128;
            while qhat * v_n2 > base * rhat + (u[j + n - 2] as u128) {
                qhat -= 1;
                rhat += v[n - 1] as u128;
                if rhat >= base {
                    break;
                }
            }
        }

        let mut borrow = 0u128;
        for i in 0..n {
            let p = (qhat as u128) * (v[i] as u128);
            let p_lo = p & (base - 1);
            let p_hi = p >> 64;
            let u_val = u[j + i] as u128;
            let (res1, overflow1) = u_val.overflowing_sub(p_lo + borrow);
            u[j + i] = res1 as u64;
            borrow = p_hi + if overflow1 { 1 } else { 0 };
        }
        let u_val = u[j + n] as u128;
        let (res2, overflow2) = u_val.overflowing_sub(borrow);
        u[j + n] = res2 as u64;
        if overflow2 {
            qhat -= 1;
            let mut carry = 0u128;
            for i in 0..n {
                let sum = u[j + i] as u128 + v[i] as u128 + carry;
                u[j + i] = sum as u64;
                carry = sum >> 64;
            }
            u[j + n] = (u[j + n] as u128 + carry) as u64;
        }
        q[j] = qhat as u64;
    }

    let mut r = u[..n].to_vec();
    if shift != 0 {
        r = shr_bits(&r, shift);
    }
    normalize_len(&mut r);
    normalize_len(&mut q);
    (q, r)
}

pub(crate) fn add_big(a: &BigNumValue, b: &BigNumValue) -> BigNumValue {
    if a.sign == 0 {
        return b.clone();
    }
    if b.sign == 0 {
        return a.clone();
    }
    if a.sign == b.sign {
        let mut out = BigNumValue {
            sign: a.sign,
            limbs: add_mag(&a.limbs, &b.limbs),
        };
        out.normalize();
        return out;
    }

    match cmp_mag_slices(&a.limbs, &b.limbs) {
        Ordering::Greater => {
            let mut out = BigNumValue {
                sign: a.sign,
                limbs: sub_mag(&a.limbs, &b.limbs),
            };
            out.normalize();
            out
        }
        Ordering::Less => {
            let mut out = BigNumValue {
                sign: b.sign,
                limbs: sub_mag(&b.limbs, &a.limbs),
            };
            out.normalize();
            out
        }
        Ordering::Equal => BigNumValue {
            sign: 0,
            limbs: Vec::new(),
        },
    }
}

pub(crate) fn cmp_big_value(a: &BigNumValue, b: &BigNumValue) -> Ordering {
    if a.sign != b.sign {
        return a.sign.cmp(&b.sign);
    }
    if a.sign == 0 {
        return Ordering::Equal;
    }
    let mag = cmp_mag_slices(&a.limbs, &b.limbs);
    if a.sign > 0 {
        mag
    } else {
        mag.reverse()
    }
}

pub(crate) fn sub_big(a: &BigNumValue, b: &BigNumValue) -> BigNumValue {
    let mut neg_b = b.clone();
    neg_b.sign = -neg_b.sign;
    add_big(a, &neg_b)
}

pub(crate) fn mul_big(a: &BigNumValue, b: &BigNumValue) -> BigNumValue {
    if a.sign == 0 || b.sign == 0 {
        return BigNumValue {
            sign: 0,
            limbs: Vec::new(),
        };
    }
    let mut out = BigNumValue {
        sign: a.sign * b.sign,
        limbs: mul_mag(&a.limbs, &b.limbs),
    };
    out.normalize();
    out
}

pub(crate) fn div_mod_big(
    a: &BigNumValue,
    b: &BigNumValue,
) -> Result<(BigNumValue, BigNumValue), RuntimeError> {
    if b.sign == 0 {
        return Err(RuntimeError::Unimplemented {
            message: "division by zero",
        });
    }
    if a.sign == 0 {
        return Ok((
            BigNumValue {
                sign: 0,
                limbs: Vec::new(),
            },
            BigNumValue {
                sign: 0,
                limbs: Vec::new(),
            },
        ));
    }

    let (q_mag, r_mag) = div_mod_mag(&a.limbs, &b.limbs);
    let mut q = BigNumValue {
        sign: a.sign * b.sign,
        limbs: q_mag,
    };
    q.normalize();

    let mut r = BigNumValue {
        sign: a.sign,
        limbs: r_mag,
    };
    r.normalize();
    Ok((q, r))
}

pub(crate) fn alloc_bignum_value(
    vm: &mut VM,
    state: &mut InterpreterState,
    value: &BigNumValue,
    scratch: &mut Vec<Value>,
) -> Result<Value, RuntimeError> {
    if value.sign == 0 {
        let bn = with_roots(vm, state, scratch, |proxy, roots| unsafe {
            alloc_bignum_from_limbs(proxy, roots, 0, &[]).value()
        });
        return Ok(bn);
    }
    let bn = with_roots(vm, state, scratch, |proxy, roots| unsafe {
        alloc_bignum_from_limbs(proxy, roots, value.sign, &value.limbs).value()
    });
    Ok(bn)
}

pub(crate) fn bignum_value_to_value(
    vm: &mut VM,
    state: &mut InterpreterState,
    value: &BigNumValue,
    scratch: &mut Vec<Value>,
    allow_fixnum: bool,
) -> Result<Value, RuntimeError> {
    if value.sign == 0 {
        if allow_fixnum {
            return Ok(Value::from_i64(0));
        }
        return alloc_bignum_value(vm, state, value, scratch);
    }
    if allow_fixnum && value.limbs.len() == 1 {
        let limb = value.limbs[0];
        match value.sign {
            1 => {
                if limb <= BigNum::FIXNUM_MAX as u64 {
                    return Ok(Value::from_i64(limb as i64));
                }
            }
            -1 => {
                let max_mag = 1_u64 << 62;
                if limb <= max_mag {
                    return Ok(Value::from_i64(-(limb as i64)));
                }
            }
            _ => {}
        }
    }
    alloc_bignum_value(vm, state, value, scratch)
}

pub fn bignum_add(
    vm: &mut VM,
    state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let rhs = args.first().copied().ok_or(RuntimeError::TypeError {
        expected: "bignum",
        got: Value::from_i64(0),
    })?;
    let a = unsafe { &*expect_bignum(receiver)? };
    let b = unsafe { &*expect_bignum(rhs)? };
    let res = add_big(&from_bignum(a), &from_bignum(b));
    let mut scratch = vec![receiver, rhs];
    alloc_bignum_value(vm, state, &res, &mut scratch)
}

pub fn bignum_sub(
    vm: &mut VM,
    state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let rhs = args.first().copied().ok_or(RuntimeError::TypeError {
        expected: "bignum",
        got: Value::from_i64(0),
    })?;
    let a = unsafe { &*expect_bignum(receiver)? };
    let b = unsafe { &*expect_bignum(rhs)? };
    let res = sub_big(&from_bignum(a), &from_bignum(b));
    let mut scratch = vec![receiver, rhs];
    alloc_bignum_value(vm, state, &res, &mut scratch)
}

pub fn bignum_mul(
    vm: &mut VM,
    state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let rhs = args.first().copied().ok_or(RuntimeError::TypeError {
        expected: "bignum",
        got: Value::from_i64(0),
    })?;
    let a = unsafe { &*expect_bignum(receiver)? };
    let b = unsafe { &*expect_bignum(rhs)? };
    let res = mul_big(&from_bignum(a), &from_bignum(b));
    let mut scratch = vec![receiver, rhs];
    alloc_bignum_value(vm, state, &res, &mut scratch)
}

pub fn bignum_div(
    vm: &mut VM,
    state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let rhs = args.first().copied().ok_or(RuntimeError::TypeError {
        expected: "bignum",
        got: Value::from_i64(0),
    })?;
    let a = unsafe { &*expect_bignum(receiver)? };
    let b = unsafe { &*expect_bignum(rhs)? };
    let a_val = from_bignum(a);
    let b_val = from_bignum(b);
    let (quot, rem) = div_mod_big(&a_val, &b_val)?;
    if rem.sign == 0 {
        let mut scratch = vec![receiver, rhs];
        return alloc_bignum_value(vm, state, &quot, &mut scratch);
    }
    ratio::make_ratio(vm, state, receiver, rhs, true)
}

pub fn bignum_mod(
    vm: &mut VM,
    state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let rhs = args.first().copied().ok_or(RuntimeError::TypeError {
        expected: "bignum",
        got: Value::from_i64(0),
    })?;
    let a = unsafe { &*expect_bignum(receiver)? };
    let b = unsafe { &*expect_bignum(rhs)? };
    let a_val = from_bignum(a);
    let b_val = from_bignum(b);
    let (_, rem) = div_mod_big(&a_val, &b_val)?;
    let mut scratch = vec![receiver, rhs];
    alloc_bignum_value(vm, state, &rem, &mut scratch)
}

pub fn bignum_neg(
    vm: &mut VM,
    state: &mut InterpreterState,
    receiver: Value,
    _args: &[Value],
) -> Result<Value, RuntimeError> {
    let a = unsafe { &*expect_bignum(receiver)? };
    let mut v = from_bignum(a);
    v.sign = -v.sign;
    let mut scratch = vec![receiver];
    alloc_bignum_value(vm, state, &v, &mut scratch)
}

pub fn bignum_to_fixnum(
    _vm: &mut VM,
    _state: &mut InterpreterState,
    receiver: Value,
    _args: &[Value],
) -> Result<Value, RuntimeError> {
    let a = unsafe { &*expect_bignum(receiver)? };
    if let Some(value) = a.to_fixnum_checked() {
        return Ok(Value::from_i64(value));
    }
    Err(RuntimeError::Unimplemented {
        message: "bignum out of fixnum range",
    })
}

pub fn bignum_to_ratio(
    vm: &mut VM,
    state: &mut InterpreterState,
    receiver: Value,
    _args: &[Value],
) -> Result<Value, RuntimeError> {
    ratio::make_ratio(vm, state, receiver, Value::from_i64(1), false)
}

pub fn bignum_to_float(
    vm: &mut VM,
    state: &mut InterpreterState,
    receiver: Value,
    _args: &[Value],
) -> Result<Value, RuntimeError> {
    let a = unsafe { &*expect_bignum(receiver)? };
    let mut value = 0.0f64;
    for &limb in a.limbs().iter().rev() {
        value = value * 18446744073709551616.0 + (limb as f64);
        if !value.is_finite() {
            return Err(RuntimeError::Unimplemented {
                message: "bignum out of float range",
            });
        }
    }
    if a.sign < 0 {
        value = -value;
    }
    let mut scratch = vec![receiver];
    let float = with_roots(vm, state, &mut scratch, |proxy, roots| unsafe {
        crate::alloc::alloc_float(proxy, roots, value).value()
    });
    Ok(float)
}

pub fn bignum_to_string(
    vm: &mut VM,
    state: &mut InterpreterState,
    receiver: Value,
    _args: &[Value],
) -> Result<Value, RuntimeError> {
    let a = unsafe { &*expect_bignum(receiver)? };
    let text = big_to_string(&from_bignum(a));
    alloc_vm_string(vm, state, text.as_bytes())
}

pub fn bignum_eq(
    vm: &mut VM,
    _state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let rhs = args.first().copied().ok_or(RuntimeError::TypeError {
        expected: "bignum",
        got: Value::from_i64(0),
    })?;
    let a = from_bignum(unsafe { &*expect_bignum(receiver)? });
    let b = from_bignum(unsafe { &*expect_bignum(rhs)? });
    Ok(bool_value(vm, cmp_big_value(&a, &b) == Ordering::Equal))
}

pub fn bignum_ne(
    vm: &mut VM,
    _state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let rhs = args.first().copied().ok_or(RuntimeError::TypeError {
        expected: "bignum",
        got: Value::from_i64(0),
    })?;
    let a = from_bignum(unsafe { &*expect_bignum(receiver)? });
    let b = from_bignum(unsafe { &*expect_bignum(rhs)? });
    Ok(bool_value(vm, cmp_big_value(&a, &b) != Ordering::Equal))
}

pub fn bignum_lt(
    vm: &mut VM,
    _state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let rhs = args.first().copied().ok_or(RuntimeError::TypeError {
        expected: "bignum",
        got: Value::from_i64(0),
    })?;
    let a = from_bignum(unsafe { &*expect_bignum(receiver)? });
    let b = from_bignum(unsafe { &*expect_bignum(rhs)? });
    Ok(bool_value(vm, cmp_big_value(&a, &b) == Ordering::Less))
}

pub fn bignum_le(
    vm: &mut VM,
    _state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let rhs = args.first().copied().ok_or(RuntimeError::TypeError {
        expected: "bignum",
        got: Value::from_i64(0),
    })?;
    let a = from_bignum(unsafe { &*expect_bignum(receiver)? });
    let b = from_bignum(unsafe { &*expect_bignum(rhs)? });
    let cmp = cmp_big_value(&a, &b);
    Ok(bool_value(
        vm,
        cmp == Ordering::Less || cmp == Ordering::Equal,
    ))
}

pub fn bignum_gt(
    vm: &mut VM,
    _state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let rhs = args.first().copied().ok_or(RuntimeError::TypeError {
        expected: "bignum",
        got: Value::from_i64(0),
    })?;
    let a = from_bignum(unsafe { &*expect_bignum(receiver)? });
    let b = from_bignum(unsafe { &*expect_bignum(rhs)? });
    Ok(bool_value(vm, cmp_big_value(&a, &b) == Ordering::Greater))
}

pub fn bignum_ge(
    vm: &mut VM,
    _state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let rhs = args.first().copied().ok_or(RuntimeError::TypeError {
        expected: "bignum",
        got: Value::from_i64(0),
    })?;
    let a = from_bignum(unsafe { &*expect_bignum(receiver)? });
    let b = from_bignum(unsafe { &*expect_bignum(rhs)? });
    let cmp = cmp_big_value(&a, &b);
    Ok(bool_value(
        vm,
        cmp == Ordering::Greater || cmp == Ordering::Equal,
    ))
}

pub(crate) fn big_to_string(value: &BigNumValue) -> String {
    if value.sign == 0 {
        return "0".to_string();
    }
    let base: u64 = 1_000_000_000;
    let base_val = BigNumValue {
        sign: 1,
        limbs: vec![base],
    };
    let mut temp = BigNumValue {
        sign: 1,
        limbs: value.limbs.clone(),
    };
    temp.normalize();
    let mut parts: Vec<u64> = Vec::new();
    while temp.sign != 0 {
        let (q, r) = div_mod_big(&temp, &base_val).expect("div_mod");
        let rem = if r.limbs.is_empty() { 0 } else { r.limbs[0] };
        parts.push(rem);
        temp = q;
    }
    let mut out = String::new();
    if value.sign < 0 {
        out.push('-');
    }
    if let Some(last) = parts.pop() {
        out.push_str(&last.to_string());
    }
    for part in parts.iter().rev() {
        out.push_str(&format!("{:09}", part));
    }
    out
}

pub(crate) fn gcd_mag(a: &[u64], b: &[u64]) -> Vec<u64> {
    let mut x = BigNumValue {
        sign: 1,
        limbs: a.to_vec(),
    };
    let mut y = BigNumValue {
        sign: 1,
        limbs: b.to_vec(),
    };
    x.normalize();
    y.normalize();
    while y.sign != 0 {
        let (_, r) = div_mod_big(&x, &y).expect("gcd divide");
        x = y;
        y = r;
    }
    x.limbs
}
