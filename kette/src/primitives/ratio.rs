use crate::{
    Allocator, BigNum, ExecutionResult, Handle, NumberError, ObjectType,
    PrimitiveContext, Ratio, Value, primitives::bool_object,
};

use crate::primitives::bignum::{
    bignum_add_raw, bignum_div_mod_raw, bignum_mul_raw, bignum_sub_raw,
    clone_bignum, cmp_bignum,
};

fn value_to_bignum(
    heap: &mut impl Allocator,
    value: Value,
) -> Option<Handle<BigNum>> {
    if let Some(fix) = value.as_tagged_fixnum::<i64>() {
        let big = heap.allocate_bignum_from_i64(fix.as_i64());
        return Some(big);
    }
    if value.is_object() {
        // SAFETY: checked
        let handle = unsafe { value.as_heap_handle_unchecked() };
        // SAFETY: checked
        if unsafe { handle.header.object_type().unwrap_unchecked() }
            == ObjectType::BigNum
        {
            // SAFETY: checked
            return Some(unsafe { handle.cast::<BigNum>() });
        }
    }
    None
}

fn is_bignum_zero(value: &BigNum) -> bool {
    value.len() == 0
}

fn is_bignum_one(value: &BigNum) -> bool {
    matches!(value.to_fixnum_checked(), Some(1))
}

fn abs_bignum(heap: &mut impl Allocator, value: &BigNum) -> Handle<BigNum> {
    if value.len() == 0 {
        return clone_bignum(heap, value, 0);
    }
    if value.sign >= 0 {
        return clone_bignum(heap, value, value.sign);
    }
    clone_bignum(heap, value, 1)
}

fn negate_bignum(heap: &mut impl Allocator, value: &BigNum) -> Handle<BigNum> {
    if value.len() == 0 {
        return clone_bignum(heap, value, 0);
    }
    clone_bignum(heap, value, -value.sign)
}

fn demote_value(value: Handle<BigNum>) -> Value {
    if let Some(fix) = value.to_fixnum_checked() {
        return Value::from_fixnum(fix);
    }
    value.into()
}

fn gcd_bignum(
    heap: &mut impl Allocator,
    a: &BigNum,
    b: &BigNum,
) -> Handle<BigNum> {
    let mut x = abs_bignum(heap, a);
    let mut y = abs_bignum(heap, b);
    while !is_bignum_zero(&y) {
        let (_, r) = bignum_div_mod_raw(heap, &x, &y).expect("gcd divide");
        x = y;
        y = r;
    }
    x
}

pub(crate) fn make_ratio_from_values(
    heap: &mut impl Allocator,
    numerator: Value,
    denominator: Value,
) -> Result<Handle<Value>, NumberError> {
    let Some(numer) = value_to_bignum(heap, numerator) else {
        return Err(NumberError::Overflow);
    };
    let Some(denom) = value_to_bignum(heap, denominator) else {
        return Err(NumberError::Overflow);
    };
    make_ratio_from_bignums(heap, numer, denom)
}

fn make_ratio_from_bignums(
    heap: &mut impl Allocator,
    numerator: Handle<BigNum>,
    denominator: Handle<BigNum>,
) -> Result<Handle<Value>, NumberError> {
    if is_bignum_zero(&denominator) {
        return Err(NumberError::DivisionByZero);
    }
    if is_bignum_zero(&numerator) {
        // SAFETY: fixnum range already checked
        return Ok(unsafe { Value::from_fixnum(0).as_handle_unchecked() });
    }

    let mut num = numerator;
    let mut den = denominator;

    if den.sign < 0 {
        num = negate_bignum(heap, &num);
        den = negate_bignum(heap, &den);
    }

    let gcd = gcd_bignum(heap, &num, &den);
    if !is_bignum_one(&gcd) {
        let (num_q, num_r) = bignum_div_mod_raw(heap, &num, &gcd)?;
        let (den_q, den_r) = bignum_div_mod_raw(heap, &den, &gcd)?;
        debug_assert!(is_bignum_zero(&num_r));
        debug_assert!(is_bignum_zero(&den_r));
        num = num_q;
        den = den_q;
    }

    if is_bignum_one(&den) {
        // SAFETY: fixnum range already checked when demoted
        return Ok(unsafe { demote_value(num).as_handle_unchecked() });
    }

    let ratio = heap.allocate_ratio(demote_value(num), demote_value(den));
    Ok(ratio.into())
}

pub fn is_ratio(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let res = is_ratio_object(ctx.receiver);
    ctx.outputs[0] = bool_object(ctx, res);
    ExecutionResult::Normal
}

pub fn is_2ratio(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let res1 = is_ratio_object(ctx.receiver);
    let res2 = is_ratio_object(ctx.inputs[0]);
    ctx.outputs[0] = bool_object(ctx, res1 && res2);
    ExecutionResult::Normal
}

fn is_ratio_object(obj: Handle<Value>) -> bool {
    if obj.is_fixnum() {
        return false;
    }
    // SAFETY: checked
    if let Some(ty) = unsafe { obj.as_heap_value_handle().header.object_type() }
    {
        return ty == ObjectType::Ratio;
    }
    false
}

pub fn ratio_new(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let numerator = ctx.inputs[0].inner();
    let denominator = ctx.receiver.inner();
    match make_ratio_from_values(ctx.heap, numerator, denominator) {
        Ok(res) => ctx.outputs[0] = res,
        Err(NumberError::DivisionByZero) => {
            return ExecutionResult::NumberError(NumberError::DivisionByZero);
        }
        Err(NumberError::Overflow) => {
            return ExecutionResult::Panic(
                "ratioNew: numerator and denominator must be integers"
                    .to_string(),
            );
        }
    }
    ExecutionResult::Normal
}

pub fn ratio_numerator(ctx: &mut PrimitiveContext) -> ExecutionResult {
    // SAFETY: caller must ensure receiver is ratio
    let ratio = unsafe { ctx.receiver.cast::<Ratio>() };
    ctx.outputs[0] = unsafe { ratio.numerator.as_handle_unchecked() };
    ExecutionResult::Normal
}

pub fn ratio_denominator(ctx: &mut PrimitiveContext) -> ExecutionResult {
    // SAFETY: caller must ensure receiver is ratio
    let ratio = unsafe { ctx.receiver.cast::<Ratio>() };
    ctx.outputs[0] = unsafe { ratio.denominator.as_handle_unchecked() };
    ExecutionResult::Normal
}

pub fn ratio_add(ctx: &mut PrimitiveContext) -> ExecutionResult {
    // SAFETY: caller must ensure receiver is ratio
    let rhs = unsafe { ctx.receiver.cast::<Ratio>() };
    // SAFETY: caller must ensure input is ratio
    let lhs = unsafe { ctx.inputs[0].cast::<Ratio>() };
    match ratio_add_raw(ctx.heap, lhs, rhs) {
        Ok(res) => ctx.outputs[0] = res,
        Err(err) => return ExecutionResult::NumberError(err),
    }
    ExecutionResult::Normal
}

pub fn ratio_sub(ctx: &mut PrimitiveContext) -> ExecutionResult {
    // SAFETY: caller must ensure receiver is ratio
    let rhs = unsafe { ctx.receiver.cast::<Ratio>() };
    // SAFETY: caller must ensure input is ratio
    let lhs = unsafe { ctx.inputs[0].cast::<Ratio>() };
    match ratio_sub_raw(ctx.heap, lhs, rhs) {
        Ok(res) => ctx.outputs[0] = res,
        Err(err) => return ExecutionResult::NumberError(err),
    }
    ExecutionResult::Normal
}

pub fn ratio_mul(ctx: &mut PrimitiveContext) -> ExecutionResult {
    // SAFETY: caller must ensure receiver is ratio
    let rhs = unsafe { ctx.receiver.cast::<Ratio>() };
    // SAFETY: caller must ensure input is ratio
    let lhs = unsafe { ctx.inputs[0].cast::<Ratio>() };
    match ratio_mul_raw(ctx.heap, lhs, rhs) {
        Ok(res) => ctx.outputs[0] = res,
        Err(err) => return ExecutionResult::NumberError(err),
    }
    ExecutionResult::Normal
}

pub fn ratio_div(ctx: &mut PrimitiveContext) -> ExecutionResult {
    // SAFETY: caller must ensure receiver is ratio
    let rhs = unsafe { ctx.receiver.cast::<Ratio>() };
    // SAFETY: caller must ensure input is ratio
    let lhs = unsafe { ctx.inputs[0].cast::<Ratio>() };
    match ratio_div_raw(ctx.heap, lhs, rhs) {
        Ok(res) => ctx.outputs[0] = res,
        Err(err) => return ExecutionResult::NumberError(err),
    }
    ExecutionResult::Normal
}

pub fn ratio_neg(ctx: &mut PrimitiveContext) -> ExecutionResult {
    // SAFETY: caller must ensure receiver is ratio
    let ratio = unsafe { ctx.receiver.cast::<Ratio>() };
    let Some(numer) = value_to_bignum(ctx.heap, ratio.numerator) else {
        return ExecutionResult::Panic(
            "ratio: numerator must be an integer".to_string(),
        );
    };
    let Some(denom) = value_to_bignum(ctx.heap, ratio.denominator) else {
        return ExecutionResult::Panic(
            "ratio: denominator must be an integer".to_string(),
        );
    };

    let numer = negate_bignum(ctx.heap, &numer);
    match make_ratio_from_bignums(ctx.heap, numer, denom) {
        Ok(res) => ctx.outputs[0] = res,
        Err(err) => return ExecutionResult::NumberError(err),
    }
    ExecutionResult::Normal
}

pub fn ratio_eq(ctx: &mut PrimitiveContext) -> ExecutionResult {
    ratio_cmp(ctx, |ord| ord == std::cmp::Ordering::Equal)
}

pub fn ratio_neq(ctx: &mut PrimitiveContext) -> ExecutionResult {
    ratio_cmp(ctx, |ord| ord != std::cmp::Ordering::Equal)
}

pub fn ratio_lt(ctx: &mut PrimitiveContext) -> ExecutionResult {
    ratio_cmp(ctx, |ord| ord == std::cmp::Ordering::Less)
}

pub fn ratio_gt(ctx: &mut PrimitiveContext) -> ExecutionResult {
    ratio_cmp(ctx, |ord| ord == std::cmp::Ordering::Greater)
}

pub fn ratio_leq(ctx: &mut PrimitiveContext) -> ExecutionResult {
    ratio_cmp(ctx, |ord| {
        ord == std::cmp::Ordering::Less || ord == std::cmp::Ordering::Equal
    })
}

pub fn ratio_geq(ctx: &mut PrimitiveContext) -> ExecutionResult {
    ratio_cmp(ctx, |ord| {
        ord == std::cmp::Ordering::Greater || ord == std::cmp::Ordering::Equal
    })
}

fn ratio_cmp(
    ctx: &mut PrimitiveContext,
    f: impl FnOnce(std::cmp::Ordering) -> bool,
) -> ExecutionResult {
    // SAFETY: caller must ensure receiver is ratio
    let rhs = unsafe { ctx.receiver.cast::<Ratio>() };
    // SAFETY: caller must ensure input is ratio
    let lhs = unsafe { ctx.inputs[0].cast::<Ratio>() };
    let ord = match ratio_cmp_raw(ctx.heap, lhs, rhs) {
        Ok(ord) => ord,
        Err(err) => return err,
    };
    ctx.outputs[0] = bool_object(ctx, f(ord));
    ExecutionResult::Normal
}

pub(crate) fn ratio_add_raw(
    heap: &mut impl Allocator,
    lhs: Handle<Ratio>,
    rhs: Handle<Ratio>,
) -> Result<Handle<Value>, NumberError> {
    let (a_num, a_den) = ratio_components_raw(heap, lhs)?;
    let (b_num, b_den) = ratio_components_raw(heap, rhs)?;

    let left = bignum_mul_raw(heap, &a_num, &b_den);
    let right = bignum_mul_raw(heap, &b_num, &a_den);
    let numer = bignum_add_raw(heap, &left, &right);
    let denom = bignum_mul_raw(heap, &a_den, &b_den);
    make_ratio_from_bignums(heap, numer, denom)
}

pub(crate) fn ratio_sub_raw(
    heap: &mut impl Allocator,
    lhs: Handle<Ratio>,
    rhs: Handle<Ratio>,
) -> Result<Handle<Value>, NumberError> {
    let (a_num, a_den) = ratio_components_raw(heap, lhs)?;
    let (b_num, b_den) = ratio_components_raw(heap, rhs)?;

    let left = bignum_mul_raw(heap, &a_num, &b_den);
    let right = bignum_mul_raw(heap, &b_num, &a_den);
    let numer = bignum_sub_raw(heap, &left, &right);
    let denom = bignum_mul_raw(heap, &a_den, &b_den);
    make_ratio_from_bignums(heap, numer, denom)
}

pub(crate) fn ratio_mul_raw(
    heap: &mut impl Allocator,
    lhs: Handle<Ratio>,
    rhs: Handle<Ratio>,
) -> Result<Handle<Value>, NumberError> {
    let (a_num, a_den) = ratio_components_raw(heap, lhs)?;
    let (b_num, b_den) = ratio_components_raw(heap, rhs)?;

    let numer = bignum_mul_raw(heap, &a_num, &b_num);
    let denom = bignum_mul_raw(heap, &a_den, &b_den);
    make_ratio_from_bignums(heap, numer, denom)
}

pub(crate) fn ratio_div_raw(
    heap: &mut impl Allocator,
    lhs: Handle<Ratio>,
    rhs: Handle<Ratio>,
) -> Result<Handle<Value>, NumberError> {
    let (a_num, a_den) = ratio_components_raw(heap, lhs)?;
    let (b_num, b_den) = ratio_components_raw(heap, rhs)?;

    if is_bignum_zero(&b_num) {
        return Err(NumberError::DivisionByZero);
    }

    let numer = bignum_mul_raw(heap, &a_num, &b_den);
    let denom = bignum_mul_raw(heap, &a_den, &b_num);
    make_ratio_from_bignums(heap, numer, denom)
}

pub(crate) fn ratio_cmp_raw(
    heap: &mut impl Allocator,
    lhs: Handle<Ratio>,
    rhs: Handle<Ratio>,
) -> Result<std::cmp::Ordering, ExecutionResult> {
    let (a_num, a_den) = ratio_components_raw(heap, lhs).map_err(|_| {
        ExecutionResult::Panic(
            "ratio: numerator or denominator must be an integer".to_string(),
        )
    })?;
    let (b_num, b_den) = ratio_components_raw(heap, rhs).map_err(|_| {
        ExecutionResult::Panic(
            "ratio: numerator or denominator must be an integer".to_string(),
        )
    })?;

    let left = bignum_mul_raw(heap, &a_num, &b_den);
    let right = bignum_mul_raw(heap, &b_num, &a_den);
    Ok(cmp_bignum(&left, &right))
}

fn ratio_components_raw(
    heap: &mut impl Allocator,
    ratio: Handle<Ratio>,
) -> Result<(Handle<BigNum>, Handle<BigNum>), NumberError> {
    let Some(numer) = value_to_bignum(heap, ratio.numerator) else {
        return Err(NumberError::Overflow);
    };
    let Some(denom) = value_to_bignum(heap, ratio.denominator) else {
        return Err(NumberError::Overflow);
    };
    Ok((numer, denom))
}

fn bignum_to_f64(value: &BigNum) -> Option<f64> {
    let mut result = 0.0f64;
    for &limb in value.limbs().iter().rev() {
        result = result * 18446744073709551616.0 + (limb as f64);
        if !result.is_finite() {
            return None;
        }
    }
    if value.sign < 0 {
        result = -result;
    }
    Some(result)
}

fn bignum_to_decimal_string(
    heap: &mut impl Allocator,
    value: &BigNum,
) -> String {
    if value.len() == 0 {
        return "0".to_string();
    }

    let mut current = abs_bignum(heap, value);
    let base = heap.allocate_bignum_from_u64(1_000_000_000);
    let mut parts: Vec<u32> = Vec::new();

    while !is_bignum_zero(&current) {
        let (q, r) = bignum_div_mod_raw(heap, &current, &base)
            .expect("decimal conversion divide");
        let digit =
            r.to_fixnum_checked().expect("remainder fits in fixnum") as u32;
        parts.push(digit);
        current = q;
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

pub fn ratio_to_float(ctx: &mut PrimitiveContext) -> ExecutionResult {
    // SAFETY: caller must ensure receiver is ratio
    let ratio = unsafe { ctx.receiver.cast::<Ratio>() };
    let Some(numer) = value_to_bignum(ctx.heap, ratio.numerator) else {
        return ExecutionResult::Panic(
            "ratio>float: numerator must be an integer".to_string(),
        );
    };
    let Some(denom) = value_to_bignum(ctx.heap, ratio.denominator) else {
        return ExecutionResult::Panic(
            "ratio>float: denominator must be an integer".to_string(),
        );
    };
    let Some(numer_f) = bignum_to_f64(&numer) else {
        return ExecutionResult::Panic(
            "ratio>float: numerator out of range".to_string(),
        );
    };
    let Some(denom_f) = bignum_to_f64(&denom) else {
        return ExecutionResult::Panic(
            "ratio>float: denominator out of range".to_string(),
        );
    };
    if denom_f == 0.0 {
        return ExecutionResult::NumberError(NumberError::DivisionByZero);
    }
    let res = numer_f / denom_f;
    if !res.is_finite() {
        return ExecutionResult::Panic(
            "ratio>float: result not finite".to_string(),
        );
    }
    let float = ctx.heap.allocate_float(res);
    ctx.outputs[0] = float.into();
    ExecutionResult::Normal
}

pub fn ratio_to_string(ctx: &mut PrimitiveContext) -> ExecutionResult {
    // SAFETY: caller must ensure receiver is ratio
    let ratio = unsafe { ctx.receiver.cast::<Ratio>() };
    let Some(numer) = value_to_bignum(ctx.heap, ratio.numerator) else {
        return ExecutionResult::Panic(
            "ratio>string: numerator must be an integer".to_string(),
        );
    };
    let Some(denom) = value_to_bignum(ctx.heap, ratio.denominator) else {
        return ExecutionResult::Panic(
            "ratio>string: denominator must be an integer".to_string(),
        );
    };

    let numer_str = bignum_to_decimal_string(ctx.heap, &numer);
    let denom_str = bignum_to_decimal_string(ctx.heap, &denom);
    let mut out = String::new();
    out.push_str(&numer_str);
    out.push('/');
    out.push_str(&denom_str);

    let ba = ctx.heap.allocate_aligned_bytearray(out.as_bytes(), 8);
    let string = ctx.heap.allocate_string(ba);
    ctx.outputs[0] = string.into();
    ExecutionResult::Normal
}

pub fn parent(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let p = ctx.vm.specials().ratio_traits;
    ctx.outputs[0] = p.into();
    ExecutionResult::Normal
}

#[cfg(test)]
mod tests {
    use crate::{Allocator, Heap, HeapSettings, Value};

    use super::{
        make_ratio_from_values, ratio_add_raw, ratio_div_raw, ratio_mul_raw,
        ratio_sub_raw,
    };

    #[test]
    fn ratio_reduces_and_demotes() {
        let heap = Heap::new(HeapSettings::default());
        let mut heap = heap.proxy();

        let numer = Value::from_fixnum(2);
        let denom = Value::from_fixnum(4);
        let ratio = make_ratio_from_values(&mut heap, numer, denom).unwrap();
        let val = ratio.as_value();
        assert!(val.is_object());

        let handle = unsafe { val.as_heap_handle_unchecked() };
        let ratio = unsafe { handle.cast::<crate::Ratio>() };
        assert_eq!(
            ratio.numerator.as_tagged_fixnum::<i64>().unwrap().as_i64(),
            1
        );
        assert_eq!(
            ratio
                .denominator
                .as_tagged_fixnum::<i64>()
                .unwrap()
                .as_i64(),
            2
        );

        let numer = Value::from_fixnum(4);
        let denom = Value::from_fixnum(2);
        let ratio = make_ratio_from_values(&mut heap, numer, denom).unwrap();
        let val = ratio.as_value();
        assert!(val.is_fixnum());
        assert_eq!(val.as_tagged_fixnum::<i64>().unwrap().as_i64(), 2);
    }

    #[test]
    fn ratio_adds() {
        let heap = Heap::new(HeapSettings::default());
        let mut heap = heap.proxy();

        let a = make_ratio_from_values(
            &mut heap,
            Value::from_fixnum(1),
            Value::from_fixnum(2),
        )
        .unwrap();
        let b = make_ratio_from_values(
            &mut heap,
            Value::from_fixnum(1),
            Value::from_fixnum(3),
        )
        .unwrap();

        let a_ratio = unsafe { a.as_value().as_heap_handle_unchecked().cast() };
        let b_ratio = unsafe { b.as_value().as_heap_handle_unchecked().cast() };

        let result = ratio_add_raw(&mut heap, a_ratio, b_ratio).unwrap();
        let ratio = unsafe {
            result
                .as_value()
                .as_heap_handle_unchecked()
                .cast::<crate::Ratio>()
        };
        assert_eq!(
            ratio.numerator.as_tagged_fixnum::<i64>().unwrap().as_i64(),
            5
        );
        assert_eq!(
            ratio
                .denominator
                .as_tagged_fixnum::<i64>()
                .unwrap()
                .as_i64(),
            6
        );
    }

    #[test]
    fn ratio_mul_and_div() {
        let heap = Heap::new(HeapSettings::default());
        let mut heap = heap.proxy();

        let a = make_ratio_from_values(
            &mut heap,
            Value::from_fixnum(2),
            Value::from_fixnum(3),
        )
        .unwrap();
        let b = make_ratio_from_values(
            &mut heap,
            Value::from_fixnum(3),
            Value::from_fixnum(5),
        )
        .unwrap();

        let a_ratio = unsafe { a.as_value().as_heap_handle_unchecked().cast() };
        let b_ratio = unsafe { b.as_value().as_heap_handle_unchecked().cast() };

        let result = ratio_mul_raw(&mut heap, a_ratio, b_ratio).unwrap();
        let ratio = unsafe {
            result
                .as_value()
                .as_heap_handle_unchecked()
                .cast::<crate::Ratio>()
        };
        assert_eq!(
            ratio.numerator.as_tagged_fixnum::<i64>().unwrap().as_i64(),
            2
        );
        assert_eq!(
            ratio
                .denominator
                .as_tagged_fixnum::<i64>()
                .unwrap()
                .as_i64(),
            5
        );

        let result = ratio_div_raw(&mut heap, a_ratio, b_ratio).unwrap();
        let ratio = unsafe {
            result
                .as_value()
                .as_heap_handle_unchecked()
                .cast::<crate::Ratio>()
        };
        assert_eq!(
            ratio.numerator.as_tagged_fixnum::<i64>().unwrap().as_i64(),
            10
        );
        assert_eq!(
            ratio
                .denominator
                .as_tagged_fixnum::<i64>()
                .unwrap()
                .as_i64(),
            9
        );
    }

    #[test]
    fn ratio_subtracts() {
        let heap = Heap::new(HeapSettings::default());
        let mut heap = heap.proxy();

        let a = make_ratio_from_values(
            &mut heap,
            Value::from_fixnum(3),
            Value::from_fixnum(4),
        )
        .unwrap();
        let b = make_ratio_from_values(
            &mut heap,
            Value::from_fixnum(1),
            Value::from_fixnum(2),
        )
        .unwrap();

        let a_ratio = unsafe { a.as_value().as_heap_handle_unchecked().cast() };
        let b_ratio = unsafe { b.as_value().as_heap_handle_unchecked().cast() };

        let result = ratio_sub_raw(&mut heap, a_ratio, b_ratio).unwrap();
        let ratio = unsafe {
            result
                .as_value()
                .as_heap_handle_unchecked()
                .cast::<crate::Ratio>()
        };
        assert_eq!(
            ratio.numerator.as_tagged_fixnum::<i64>().unwrap().as_i64(),
            1
        );
        assert_eq!(
            ratio
                .denominator
                .as_tagged_fixnum::<i64>()
                .unwrap()
                .as_i64(),
            4
        );
    }

    #[test]
    fn ratio_zero_denominator_errors() {
        let heap = Heap::new(HeapSettings::default());
        let mut heap = heap.proxy();
        let numer = Value::from_fixnum(1);
        let denom = Value::from_fixnum(0);
        let err = make_ratio_from_values(&mut heap, numer, denom).unwrap_err();
        assert_eq!(err, crate::NumberError::DivisionByZero);
    }

    #[test]
    fn bignum_decimal_string_formats() {
        let heap = Heap::new(HeapSettings::default());
        let mut heap = heap.proxy();

        let big = heap.allocate_bignum_from_i128(1_234_567_890_123_i128);
        let s = super::bignum_to_decimal_string(&mut heap, &big);
        assert_eq!(s, "1234567890123");

        let neg = heap.allocate_bignum_from_i128(-9_876_543_210_i128);
        let s = super::bignum_to_decimal_string(&mut heap, &neg);
        assert_eq!(s, "-9876543210");
    }
}
