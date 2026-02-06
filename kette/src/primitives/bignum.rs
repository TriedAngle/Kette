use std::cmp::Ordering;

use crate::{
    Allocator, BigNum, ExecutionResult, ObjectType, PrimitiveContext, Value,
    primitives::bool_object,
};

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

fn as_bignum(
    ctx: &mut PrimitiveContext,
    value: crate::Handle<Value>,
    name: &str,
) -> Result<crate::Handle<BigNum>, ExecutionResult> {
    if value.inner().is_fixnum() {
        let fix = unsafe { value.as_fixnum::<i64>() };
        return Ok(ctx.heap.allocate_bignum_from_i64(fix));
    }

    if value.inner().is_object() {
        let obj = unsafe { value.inner().as_heap_handle_unchecked() };
        if obj.header.object_type() == Some(ObjectType::BigNum) {
            return Ok(unsafe { obj.cast::<BigNum>() });
        }
    }

    Err(ExecutionResult::Panic(format!(
        "{name}: expected fixnum or bignum"
    )))
}

pub fn bignum_add(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let a = match as_bignum(ctx, ctx.inputs[0], "bignum+") {
        Ok(value) => value,
        Err(err) => return err,
    };
    let b = unsafe { ctx.receiver.cast::<BigNum>() };
    let result = bignum_add_raw(ctx.heap, &a, &b);
    ctx.outputs[0] = maybe_demote(result);
    ExecutionResult::Normal
}

pub fn bignum_sub(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let a = match as_bignum(ctx, ctx.inputs[0], "bignum-") {
        Ok(value) => value,
        Err(err) => return err,
    };
    let b = unsafe { ctx.receiver.cast::<BigNum>() };
    let result = bignum_sub_raw(ctx.heap, &a, &b);
    ctx.outputs[0] = maybe_demote(result);
    ExecutionResult::Normal
}

pub fn bignum_mul(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let a = match as_bignum(ctx, ctx.inputs[0], "bignum*") {
        Ok(value) => value,
        Err(err) => return err,
    };
    let b = unsafe { ctx.receiver.cast::<BigNum>() };
    let result = bignum_mul_raw(ctx.heap, &a, &b);
    ctx.outputs[0] = maybe_demote(result);
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
    let a = match as_bignum(ctx, ctx.inputs[0], "bignum=") {
        Ok(value) => value,
        Err(err) => return err,
    };
    let b = unsafe { ctx.receiver.cast::<BigNum>() };
    ctx.outputs[0] = bool_object(ctx, cmp_bignum(&a, &b) == Ordering::Equal);
    ExecutionResult::Normal
}

pub fn bignum_neq(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let a = match as_bignum(ctx, ctx.inputs[0], "bignum!=") {
        Ok(value) => value,
        Err(err) => return err,
    };
    let b = unsafe { ctx.receiver.cast::<BigNum>() };
    ctx.outputs[0] = bool_object(ctx, cmp_bignum(&a, &b) != Ordering::Equal);
    ExecutionResult::Normal
}

pub fn bignum_lt(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let a = match as_bignum(ctx, ctx.inputs[0], "bignum<") {
        Ok(value) => value,
        Err(err) => return err,
    };
    let b = unsafe { ctx.receiver.cast::<BigNum>() };
    ctx.outputs[0] = bool_object(ctx, cmp_bignum(&a, &b) == Ordering::Less);
    ExecutionResult::Normal
}

pub fn bignum_gt(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let a = match as_bignum(ctx, ctx.inputs[0], "bignum>") {
        Ok(value) => value,
        Err(err) => return err,
    };
    let b = unsafe { ctx.receiver.cast::<BigNum>() };
    ctx.outputs[0] = bool_object(ctx, cmp_bignum(&a, &b) == Ordering::Greater);
    ExecutionResult::Normal
}

pub fn bignum_leq(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let a = match as_bignum(ctx, ctx.inputs[0], "bignum<=") {
        Ok(value) => value,
        Err(err) => return err,
    };
    let b = unsafe { ctx.receiver.cast::<BigNum>() };
    let ord = cmp_bignum(&a, &b);
    ctx.outputs[0] =
        bool_object(ctx, ord == Ordering::Less || ord == Ordering::Equal);
    ExecutionResult::Normal
}

pub fn bignum_geq(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let a = match as_bignum(ctx, ctx.inputs[0], "bignum>=") {
        Ok(value) => value,
        Err(err) => return err,
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
        bignum_add_raw, bignum_mul_raw, bignum_sub_raw, cmp_bignum,
        normalize_len,
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
}
