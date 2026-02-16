use std::cmp::Ordering;

use crate::{
    Allocator, BigNum, ExecutionResult, Handle, NumberError, PrimitiveContext,
    Value, primitives::bool_object,
};

use crate::primitives::ratio::make_ratio_from_values;

pub fn fixnum_to_bignum(ctx: &mut PrimitiveContext) -> ExecutionResult {
    if !ctx.receiver.inner().is_fixnum() {
        return ExecutionResult::Panic(
            "fixnum>bignum: receiver must be a fixnum".to_string(),
        );
    }
    let value = unsafe { ctx.receiver.as_fixnum::<i64>() };
    let big = ctx.heap.allocate_bignum_from_i64(value);
    ctx.outputs[0] = big.into();
    ExecutionResult::Normal
}

pub fn bignum_to_fixnum_checked(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let bignum = unsafe { ctx.receiver.cast::<BigNum>() };
    if let Some(value) = bignum.to_fixnum_checked() {
        ctx.outputs[0] =
            unsafe { Value::from_fixnum(value).as_handle_unchecked() };
        return ExecutionResult::Normal;
    }
    ctx.outputs[0] = bool_object(ctx, false);
    ExecutionResult::Normal
}

pub fn bignum_to_float(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let bignum = unsafe { ctx.receiver.cast::<BigNum>() };
    let mut value = 0.0f64;
    for &limb in bignum.limbs().iter().rev() {
        value = value * 18446744073709551616.0 + (limb as f64);
        if !value.is_finite() {
            return ExecutionResult::Panic(
                "bignum>float: value out of range".to_string(),
            );
        }
    }
    if bignum.sign < 0 {
        value = -value;
    }
    let float = ctx.heap.allocate_float(value);
    ctx.outputs[0] = float.into();
    ExecutionResult::Normal
}

pub fn parent(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let p = ctx.vm.specials().bignum_traits;
    ctx.outputs[0] = p.into();
    ExecutionResult::Normal
}

pub(crate) fn normalize_len(limbs: &[u64]) -> usize {
    let mut idx = limbs.len();
    while idx > 0 {
        if limbs[idx - 1] != 0 {
            break;
        }
        idx -= 1;
    }
    idx
}

fn cmp_mag_slices(a: &[u64], b: &[u64]) -> Ordering {
    let a_len = normalize_len(a);
    let b_len = normalize_len(b);
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
    let q_len = normalize_len(&q);
    q.truncate(q_len);
    if rem == 0 {
        return (q, Vec::new());
    }
    (q, vec![rem as u64])
}

fn div_mod_mag(a: &[u64], b: &[u64]) -> (Vec<u64>, Vec<u64>) {
    let a_len = normalize_len(a);
    let b_len = normalize_len(b);
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
    let r_len = normalize_len(&r);
    r.truncate(r_len);
    let q_len = normalize_len(&q);
    q.truncate(q_len);
    (q, r)
}

pub(crate) fn cmp_mag(a: &BigNum, b: &BigNum) -> Ordering {
    let a_len = a.len();
    let b_len = b.len();
    if a_len != b_len {
        return a_len.cmp(&b_len);
    }
    let a_limbs = a.limbs();
    let b_limbs = b.limbs();
    for i in (0..a_len).rev() {
        let ai = a_limbs[i];
        let bi = b_limbs[i];
        if ai != bi {
            return ai.cmp(&bi);
        }
    }
    Ordering::Equal
}

pub(crate) fn add_mag_into(out: &mut [u64], a: &BigNum, b: &BigNum) {
    let a_limbs = a.limbs();
    let b_limbs = b.limbs();
    let mut carry = 0u64;
    let max_len = out.len();
    for i in 0..max_len {
        let av = if i < a_limbs.len() { a_limbs[i] } else { 0 };
        let bv = if i < b_limbs.len() { b_limbs[i] } else { 0 };
        let sum = (av as u128) + (bv as u128) + (carry as u128);
        out[i] = sum as u64;
        carry = (sum >> 64) as u64;
    }
}

pub(crate) fn sub_mag_into(out: &mut [u64], a: &BigNum, b: &BigNum) {
    let a_limbs = a.limbs();
    let b_limbs = b.limbs();
    let mut borrow = 0u64;
    for i in 0..out.len() {
        let av = if i < a_limbs.len() { a_limbs[i] } else { 0 };
        let bv = if i < b_limbs.len() { b_limbs[i] } else { 0 };
        let (res1, overflow1) = av.overflowing_sub(bv);
        let (res2, overflow2) = res1.overflowing_sub(borrow);
        out[i] = res2;
        borrow = (overflow1 as u64) | (overflow2 as u64);
    }
}

pub(crate) fn mul_mag_into(out: &mut [u64], a: &BigNum, b: &BigNum) {
    let a_limbs = a.limbs();
    let b_limbs = b.limbs();
    for i in 0..a_limbs.len() {
        let mut carry = 0u128;
        let av = a_limbs[i] as u128;
        for j in 0..b_limbs.len() {
            let idx = i + j;
            let acc = out[idx] as u128 + av * (b_limbs[j] as u128) + carry;
            out[idx] = acc as u64;
            carry = acc >> 64;
        }
        let idx = i + b_limbs.len();
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
}

pub(crate) fn alloc_bignum_zeroed(
    heap: &mut impl Allocator,
    sign: i8,
    len: usize,
) -> crate::Handle<BigNum> {
    let layout = BigNum::required_layout(len);
    let mut obj = unsafe { heap.allocate_handle::<BigNum>(layout) };
    obj.init_zeroed(sign, len);
    obj
}

pub(crate) fn clone_bignum(
    heap: &mut impl Allocator,
    value: &BigNum,
    sign: i8,
) -> crate::Handle<BigNum> {
    let len = value.len();
    let mut out = alloc_bignum_zeroed(heap, sign, len);
    if len > 0 {
        out.limbs_mut().copy_from_slice(value.limbs());
    }
    out
}

pub(crate) fn bignum_add_raw(
    heap: &mut impl Allocator,
    a: &BigNum,
    b: &BigNum,
) -> crate::Handle<BigNum> {
    if a.len() == 0 {
        return clone_bignum(heap, b, b.sign);
    }
    if b.len() == 0 {
        return clone_bignum(heap, a, a.sign);
    }
    if a.sign == b.sign {
        let max_len = a.len().max(b.len());
        let out_len = max_len + 1;
        let mut out = alloc_bignum_zeroed(heap, a.sign, out_len);
        let out_limbs = out.limbs_mut();
        add_mag_into(out_limbs, a, b);
        let new_len = normalize_len(out_limbs);
        if new_len == 0 {
            out.sign = 0;
        }
        out.len = new_len.into();
        return out;
    }

    let ordering = cmp_mag(a, b);
    let (left, right, sign) = if ordering == Ordering::Greater {
        (a, b, a.sign)
    } else if ordering == Ordering::Less {
        (b, a, b.sign)
    } else {
        let mut out = alloc_bignum_zeroed(heap, 0, 0);
        out.sign = 0;
        out.len = 0usize.into();
        return out;
    };

    let out_len = left.len();
    let mut out = alloc_bignum_zeroed(heap, sign, out_len);
    let out_limbs = out.limbs_mut();
    sub_mag_into(out_limbs, left, right);
    let new_len = normalize_len(out_limbs);
    if new_len == 0 {
        out.sign = 0;
    }
    out.len = new_len.into();
    out
}

pub(crate) fn bignum_sub_raw(
    heap: &mut impl Allocator,
    a: &BigNum,
    b: &BigNum,
) -> crate::Handle<BigNum> {
    if b.len() == 0 {
        return clone_bignum(heap, a, a.sign);
    }
    if a.len() == 0 {
        return clone_bignum(heap, b, -b.sign);
    }

    if a.sign != b.sign {
        let max_len = a.len().max(b.len());
        let out_len = max_len + 1;
        let mut out = alloc_bignum_zeroed(heap, a.sign, out_len);
        let out_limbs = out.limbs_mut();
        add_mag_into(out_limbs, a, b);
        let new_len = normalize_len(out_limbs);
        if new_len == 0 {
            out.sign = 0;
        }
        out.len = new_len.into();
        return out;
    }

    let ordering = cmp_mag(a, b);
    let (left, right, sign) = if ordering == Ordering::Greater {
        (a, b, a.sign)
    } else if ordering == Ordering::Less {
        (b, a, -b.sign)
    } else {
        let mut out = alloc_bignum_zeroed(heap, 0, 0);
        out.sign = 0;
        out.len = 0usize.into();
        return out;
    };

    let out_len = left.len();
    let mut out = alloc_bignum_zeroed(heap, sign, out_len);
    let out_limbs = out.limbs_mut();
    sub_mag_into(out_limbs, left, right);
    let new_len = normalize_len(out_limbs);
    if new_len == 0 {
        out.sign = 0;
    }
    out.len = new_len.into();
    out
}

pub(crate) fn bignum_mul_raw(
    heap: &mut impl Allocator,
    a: &BigNum,
    b: &BigNum,
) -> crate::Handle<BigNum> {
    if a.len() == 0 || b.len() == 0 {
        return alloc_bignum_zeroed(heap, 0, 0);
    }
    let out_len = a.len() + b.len();
    let mut out = alloc_bignum_zeroed(heap, a.sign * b.sign, out_len);
    let out_limbs = out.limbs_mut();
    mul_mag_into(out_limbs, a, b);
    let new_len = normalize_len(out_limbs);
    if new_len == 0 {
        out.sign = 0;
    }
    out.len = new_len.into();
    out
}

pub(crate) fn bignum_div_mod_raw(
    heap: &mut impl Allocator,
    a: &BigNum,
    b: &BigNum,
) -> Result<(crate::Handle<BigNum>, crate::Handle<BigNum>), NumberError> {
    if b.len() == 0 {
        return Err(NumberError::DivisionByZero);
    }
    if a.len() == 0 {
        let zero = alloc_bignum_zeroed(heap, 0, 0);
        let rem = alloc_bignum_zeroed(heap, 0, 0);
        return Ok((zero, rem));
    }

    let (q_mag, r_mag) = div_mod_mag(a.limbs(), b.limbs());
    let q_sign = if q_mag.is_empty() { 0 } else { a.sign * b.sign };
    let r_sign = if r_mag.is_empty() { 0 } else { a.sign };

    let mut q = alloc_bignum_zeroed(heap, q_sign, q_mag.len());
    if !q_mag.is_empty() {
        q.limbs_mut().copy_from_slice(&q_mag);
    }
    let mut r = alloc_bignum_zeroed(heap, r_sign, r_mag.len());
    if !r_mag.is_empty() {
        r.limbs_mut().copy_from_slice(&r_mag);
    }
    Ok((q, r))
}

pub(crate) fn cmp_bignum(a: &BigNum, b: &BigNum) -> Ordering {
    if a.sign != b.sign {
        return a.sign.cmp(&b.sign);
    }
    match a.sign {
        0 => Ordering::Equal,
        1 => cmp_mag(a, b),
        -1 => cmp_mag(b, a),
        _ => Ordering::Equal,
    }
}

fn maybe_demote(value: crate::Handle<BigNum>) -> crate::Handle<Value> {
    if let Some(fix) = value.to_fixnum_checked() {
        // SAFETY: fixnum range already checked
        return unsafe { Value::from_fixnum(fix).as_handle_unchecked() };
    }
    value.into()
}

pub fn bignum_add(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let a = unsafe {
        ctx.inputs[0]
            .inner()
            .as_heap_handle_unchecked()
            .cast::<BigNum>()
    };
    let b = unsafe { ctx.receiver.cast::<BigNum>() };
    let result = bignum_add_raw(ctx.heap, &a, &b);
    ctx.outputs[0] = maybe_demote(result);
    ExecutionResult::Normal
}

pub fn bignum_sub(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let a = unsafe {
        ctx.inputs[0]
            .inner()
            .as_heap_handle_unchecked()
            .cast::<BigNum>()
    };
    let b = unsafe { ctx.receiver.cast::<BigNum>() };
    let result = bignum_sub_raw(ctx.heap, &a, &b);
    ctx.outputs[0] = maybe_demote(result);
    ExecutionResult::Normal
}

pub fn bignum_mul(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let a = unsafe {
        ctx.inputs[0]
            .inner()
            .as_heap_handle_unchecked()
            .cast::<BigNum>()
    };
    let b = unsafe { ctx.receiver.cast::<BigNum>() };
    let result = bignum_mul_raw(ctx.heap, &a, &b);
    ctx.outputs[0] = maybe_demote(result);
    ExecutionResult::Normal
}

pub fn bignum_div(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let a = unsafe {
        ctx.inputs[0]
            .inner()
            .as_heap_handle_unchecked()
            .cast::<BigNum>()
    };
    let b = unsafe { ctx.receiver.cast::<BigNum>() };
    let (quot, rem) = match bignum_div_mod_raw(ctx.heap, &a, &b) {
        Ok(res) => res,
        Err(err) => return ExecutionResult::NumberError(err),
    };
    if rem.len() == 0 {
        ctx.outputs[0] = maybe_demote(quot);
        return ExecutionResult::Normal;
    }

    let numer: Handle<Value> = a.into();
    let denom: Handle<Value> = b.into();
    match make_ratio_from_values(ctx.heap, numer.inner(), denom.inner()) {
        Ok(res) => ctx.outputs[0] = res,
        Err(err) => return ExecutionResult::NumberError(err),
    }
    ExecutionResult::Normal
}

pub fn bignum_mod(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let a = unsafe {
        ctx.inputs[0]
            .inner()
            .as_heap_handle_unchecked()
            .cast::<BigNum>()
    };
    let b = unsafe { ctx.receiver.cast::<BigNum>() };
    let (_, rem) = match bignum_div_mod_raw(ctx.heap, &a, &b) {
        Ok(res) => res,
        Err(err) => return ExecutionResult::NumberError(err),
    };
    ctx.outputs[0] = maybe_demote(rem);
    ExecutionResult::Normal
}

pub fn bignum_neg(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let b = unsafe { ctx.receiver.cast::<BigNum>() };
    if b.len() == 0 {
        ctx.outputs[0] = b.into();
        return ExecutionResult::Normal;
    }
    let mut out = alloc_bignum_zeroed(ctx.heap, -b.sign, b.len());
    out.limbs_mut().copy_from_slice(b.limbs());
    ctx.outputs[0] = maybe_demote(out);
    ExecutionResult::Normal
}

pub fn bignum_eq(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let a = unsafe {
        ctx.inputs[0]
            .inner()
            .as_heap_handle_unchecked()
            .cast::<BigNum>()
    };
    let b = unsafe { ctx.receiver.cast::<BigNum>() };
    ctx.outputs[0] = bool_object(ctx, cmp_bignum(&a, &b) == Ordering::Equal);
    ExecutionResult::Normal
}

pub fn bignum_neq(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let a = unsafe {
        ctx.inputs[0]
            .inner()
            .as_heap_handle_unchecked()
            .cast::<BigNum>()
    };
    let b = unsafe { ctx.receiver.cast::<BigNum>() };
    ctx.outputs[0] = bool_object(ctx, cmp_bignum(&a, &b) != Ordering::Equal);
    ExecutionResult::Normal
}

pub fn bignum_lt(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let a = unsafe {
        ctx.inputs[0]
            .inner()
            .as_heap_handle_unchecked()
            .cast::<BigNum>()
    };
    let b = unsafe { ctx.receiver.cast::<BigNum>() };
    ctx.outputs[0] = bool_object(ctx, cmp_bignum(&a, &b) == Ordering::Less);
    ExecutionResult::Normal
}

pub fn bignum_gt(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let a = unsafe {
        ctx.inputs[0]
            .inner()
            .as_heap_handle_unchecked()
            .cast::<BigNum>()
    };
    let b = unsafe { ctx.receiver.cast::<BigNum>() };
    ctx.outputs[0] = bool_object(ctx, cmp_bignum(&a, &b) == Ordering::Greater);
    ExecutionResult::Normal
}

pub fn bignum_leq(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let a = unsafe {
        ctx.inputs[0]
            .inner()
            .as_heap_handle_unchecked()
            .cast::<BigNum>()
    };
    let b = unsafe { ctx.receiver.cast::<BigNum>() };
    let ord = cmp_bignum(&a, &b);
    ctx.outputs[0] =
        bool_object(ctx, ord == Ordering::Less || ord == Ordering::Equal);
    ExecutionResult::Normal
}

pub fn bignum_geq(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let a = unsafe {
        ctx.inputs[0]
            .inner()
            .as_heap_handle_unchecked()
            .cast::<BigNum>()
    };
    let b = unsafe { ctx.receiver.cast::<BigNum>() };
    let ord = cmp_bignum(&a, &b);
    ctx.outputs[0] =
        bool_object(ctx, ord == Ordering::Greater || ord == Ordering::Equal);
    ExecutionResult::Normal
}

#[cfg(test)]
mod tests {
    use std::cmp::Ordering;

    use crate::{Allocator, Heap, HeapSettings};

    use super::{
        bignum_add_raw, bignum_div_mod_raw, bignum_mul_raw, bignum_sub_raw,
        cmp_bignum, normalize_len,
    };

    #[test]
    fn bignum_add_basic() {
        let heap = Heap::new(HeapSettings::default());
        let mut heap = heap.proxy();

        let a = heap.allocate_bignum_from_i64(5);
        let b = heap.allocate_bignum_from_i64(7);
        let res = bignum_add_raw(&mut heap, &a, &b);

        assert_eq!(res.sign, 1);
        assert_eq!(res.len(), 1);
        assert_eq!(res.limbs()[0], 12);
    }

    #[test]
    fn bignum_add_carry_extends_len() {
        let heap = Heap::new(HeapSettings::default());
        let mut heap = heap.proxy();

        let a = heap.allocate_bignum_from_u64(u64::MAX);
        let b = heap.allocate_bignum_from_u64(1);
        let res = bignum_add_raw(&mut heap, &a, &b);

        assert_eq!(res.len(), 2);
        assert_eq!(res.limbs()[0], 0);
        assert_eq!(res.limbs()[1], 1);
    }

    #[test]
    fn bignum_sub_signs() {
        let heap = Heap::new(HeapSettings::default());
        let mut heap = heap.proxy();

        let a = heap.allocate_bignum_from_i64(4);
        let b = heap.allocate_bignum_from_i64(9);
        let res = bignum_sub_raw(&mut heap, &a, &b);

        assert_eq!(res.sign, -1);
        assert_eq!(res.len(), 1);
        assert_eq!(res.limbs()[0], 5);
    }

    #[test]
    fn bignum_mul_basic() {
        let heap = Heap::new(HeapSettings::default());
        let mut heap = heap.proxy();

        let a = heap.allocate_bignum_from_i64(-3);
        let b = heap.allocate_bignum_from_i64(7);
        let res = bignum_mul_raw(&mut heap, &a, &b);

        assert_eq!(res.sign, -1);
        assert_eq!(res.len(), 1);
        assert_eq!(res.limbs()[0], 21);
    }

    #[test]
    fn bignum_mul_cross_limb() {
        let heap = Heap::new(HeapSettings::default());
        let mut heap = heap.proxy();

        let a = heap.allocate_bignum_from_u64(1_u64 << 32);
        let b = heap.allocate_bignum_from_u64(1_u64 << 32);
        let res = bignum_mul_raw(&mut heap, &a, &b);

        assert_eq!(res.len(), 2);
        assert_eq!(res.limbs()[0], 0);
        assert_eq!(res.limbs()[1], 1);
    }

    #[test]
    fn bignum_cmp_signs() {
        let heap = Heap::new(HeapSettings::default());
        let mut heap = heap.proxy();

        let a = heap.allocate_bignum_from_i64(-2);
        let b = heap.allocate_bignum_from_i64(1);
        assert_eq!(cmp_bignum(&a, &b), Ordering::Less);
    }

    #[test]
    fn normalize_len_trims_zeroes() {
        let limbs = [1u64, 0, 0];
        assert_eq!(normalize_len(&limbs), 1);
    }

    #[test]
    fn bignum_to_fixnum_checked_after_add() {
        let heap = Heap::new(HeapSettings::default());
        let mut heap = heap.proxy();

        let a = heap.allocate_bignum_from_i64(10);
        let b = heap.allocate_bignum_from_i64(20);
        let res = bignum_add_raw(&mut heap, &a, &b);

        assert_eq!(res.to_fixnum_checked(), Some(30));
    }

    #[test]
    fn bignum_div_mod_basic() {
        let heap = Heap::new(HeapSettings::default());
        let mut heap = heap.proxy();

        let a = heap.allocate_bignum_from_i64(20);
        let b = heap.allocate_bignum_from_i64(6);
        let (q, r) = bignum_div_mod_raw(&mut heap, &a, &b).unwrap();

        assert_eq!(q.sign, 1);
        assert_eq!(q.len(), 1);
        assert_eq!(q.limbs()[0], 3);
        assert_eq!(r.sign, 1);
        assert_eq!(r.len(), 1);
        assert_eq!(r.limbs()[0], 2);
    }

    #[test]
    fn bignum_div_mod_negative_remainder_follows_dividend() {
        let heap = Heap::new(HeapSettings::default());
        let mut heap = heap.proxy();

        let a = heap.allocate_bignum_from_i64(-20);
        let b = heap.allocate_bignum_from_i64(6);
        let (q, r) = bignum_div_mod_raw(&mut heap, &a, &b).unwrap();

        assert_eq!(q.sign, -1);
        assert_eq!(q.len(), 1);
        assert_eq!(q.limbs()[0], 3);
        assert_eq!(r.sign, -1);
        assert_eq!(r.len(), 1);
        assert_eq!(r.limbs()[0], 2);
    }

    #[test]
    fn bignum_div_mod_large() {
        let heap = Heap::new(HeapSettings::default());
        let mut heap = heap.proxy();

        let a = heap.allocate_bignum_from_i128((1_i128 << 70) + 5);
        let b = heap.allocate_bignum_from_i64(9);
        let (q, r) = bignum_div_mod_raw(&mut heap, &a, &b).unwrap();
        let expected = (((1_i128 << 70) + 5) % 9) as u64;

        assert_eq!(r.sign, 1);
        assert_eq!(r.len(), 1);
        assert_eq!(r.limbs()[0], expected);
        assert!(q.len() >= 2);
    }
}
