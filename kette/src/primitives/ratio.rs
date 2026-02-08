use crate::{
    primitives::bool_object, Allocator, BigNum, ExecutionResult, Handle,
    NumberError, ObjectType, PrimitiveContext, Ratio, Value,
};

use crate::primitives::bignum::{
    bignum_add_raw, bignum_div_mod_raw, bignum_mul_raw, bignum_sub_raw,
    clone_bignum, cmp_bignum,
};

fn value_to_i64(value: Value) -> Option<i64> {
    value.as_tagged_fixnum::<i64>().map(|fix| fix.as_i64())
}

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

fn i128_to_value(heap: &mut impl Allocator, value: i128) -> Value {
    if value >= i64::MIN as i128 && value <= i64::MAX as i128 {
        return Value::from_fixnum(value as i64);
    }
    heap.allocate_bignum_from_i128(value).into()
}

fn gcd_u128(mut a: u128, mut b: u128) -> u128 {
    while b != 0 {
        let r = a % b;
        a = b;
        b = r;
    }
    a
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
    make_ratio_from_values_mode(heap, numerator, denominator, true)
}

fn make_ratio_from_values_mode(
    heap: &mut impl Allocator,
    numerator: Value,
    denominator: Value,
    allow_demote: bool,
) -> Result<Handle<Value>, NumberError> {
    if let (Some(numer), Some(denom)) =
        (value_to_i64(numerator), value_to_i64(denominator))
    {
        return make_ratio_from_i128s(
            heap,
            numer as i128,
            denom as i128,
            allow_demote,
        );
    }
    let Some(numer) = value_to_bignum(heap, numerator) else {
        return Err(NumberError::Overflow);
    };
    let Some(denom) = value_to_bignum(heap, denominator) else {
        return Err(NumberError::Overflow);
    };
    make_ratio_from_bignums(heap, numer, denom, allow_demote)
}

fn make_ratio_from_i128s(
    heap: &mut impl Allocator,
    numerator: i128,
    denominator: i128,
    allow_demote: bool,
) -> Result<Handle<Value>, NumberError> {
    if denominator == 0 {
        return Err(NumberError::DivisionByZero);
    }
    if numerator == 0 {
        if allow_demote {
            // SAFETY: fixnum range already checked
            return Ok(unsafe { Value::from_fixnum(0).as_handle_unchecked() });
        }
        let ratio =
            heap.allocate_ratio(Value::from_fixnum(0), Value::from_fixnum(1));
        return Ok(ratio.into());
    }

    let mut num = numerator;
    let mut den = denominator;

    if den < 0 {
        let Some(den_pos) = den.checked_neg() else {
            let numer = heap.allocate_bignum_from_i128(num);
            let denom = heap.allocate_bignum_from_i128(den);
            return make_ratio_from_bignums(heap, numer, denom, allow_demote);
        };
        let Some(num_pos) = num.checked_neg() else {
            let numer = heap.allocate_bignum_from_i128(num);
            let denom = heap.allocate_bignum_from_i128(den);
            return make_ratio_from_bignums(heap, numer, denom, allow_demote);
        };
        num = num_pos;
        den = den_pos;
    }

    let num_abs = num.unsigned_abs();
    let den_abs = den.unsigned_abs();
    let gcd = gcd_u128(num_abs, den_abs);
    if gcd > i128::MAX as u128 {
        let numer = heap.allocate_bignum_from_i128(num);
        let denom = heap.allocate_bignum_from_i128(den);
        return make_ratio_from_bignums(heap, numer, denom, allow_demote);
    }
    let gcd_i128 = gcd as i128;
    if gcd_i128 > 1 {
        num /= gcd_i128;
        den /= gcd_i128;
    }

    if den == 1 {
        if allow_demote {
            // SAFETY: fixnum range already checked when demoted
            return Ok(unsafe {
                i128_to_value(heap, num).as_handle_unchecked()
            });
        }
        let numer = i128_to_value(heap, num);
        let ratio = heap.allocate_ratio(numer, Value::from_fixnum(1));
        return Ok(ratio.into());
    }

    let numer = i128_to_value(heap, num);
    let denom = i128_to_value(heap, den);
    let ratio = heap.allocate_ratio(numer, denom);
    Ok(ratio.into())
}

fn make_ratio_from_bignums(
    heap: &mut impl Allocator,
    numerator: Handle<BigNum>,
    denominator: Handle<BigNum>,
    allow_demote: bool,
) -> Result<Handle<Value>, NumberError> {
    if is_bignum_zero(&denominator) {
        return Err(NumberError::DivisionByZero);
    }
    if is_bignum_zero(&numerator) {
        if allow_demote {
            // SAFETY: fixnum range already checked
            return Ok(unsafe { Value::from_fixnum(0).as_handle_unchecked() });
        }
        let ratio =
            heap.allocate_ratio(Value::from_fixnum(0), Value::from_fixnum(1));
        return Ok(ratio.into());
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
        if allow_demote {
            // SAFETY: fixnum range already checked when demoted
            return Ok(unsafe { demote_value(num).as_handle_unchecked() });
        }
        let ratio =
            heap.allocate_ratio(demote_value(num), Value::from_fixnum(1));
        return Ok(ratio.into());
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

pub fn fixnum_to_ratio(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let numerator = ctx.receiver.inner();
    let denominator = Value::from_fixnum(1);
    match make_ratio_from_values_mode(ctx.heap, numerator, denominator, false) {
        Ok(res) => ctx.outputs[0] = res,
        Err(err) => return ExecutionResult::NumberError(err),
    }
    ExecutionResult::Normal
}

pub fn bignum_to_ratio(ctx: &mut PrimitiveContext) -> ExecutionResult {
    // SAFETY: caller ensures receiver is bignum
    let _bignum = unsafe { ctx.receiver.cast::<BigNum>() };
    let numerator = ctx.receiver.inner();
    let denominator = Value::from_fixnum(1);
    match make_ratio_from_values_mode(ctx.heap, numerator, denominator, false) {
        Ok(res) => ctx.outputs[0] = res,
        Err(err) => return ExecutionResult::NumberError(err),
    }
    ExecutionResult::Normal
}

pub fn ratio_to_fixnum(ctx: &mut PrimitiveContext) -> ExecutionResult {
    // SAFETY: caller must ensure receiver is ratio
    let ratio = unsafe { ctx.receiver.cast::<Ratio>() };
    if let (Some(numer), Some(denom)) = (
        value_to_i64(ratio.numerator),
        value_to_i64(ratio.denominator),
    ) {
        if denom != 1 {
            ctx.outputs[0] = bool_object(ctx, false);
            return ExecutionResult::Normal;
        }
        ctx.outputs[0] =
            unsafe { Value::from_fixnum(numer).as_handle_unchecked() };
        return ExecutionResult::Normal;
    }
    let Some(numer) = value_to_bignum(ctx.heap, ratio.numerator) else {
        return ExecutionResult::Panic(
            "ratio>fixnum: numerator must be an integer".to_string(),
        );
    };
    let Some(denom) = value_to_bignum(ctx.heap, ratio.denominator) else {
        return ExecutionResult::Panic(
            "ratio>fixnum: denominator must be an integer".to_string(),
        );
    };

    if !is_bignum_one(&denom) {
        ctx.outputs[0] = bool_object(ctx, false);
        return ExecutionResult::Normal;
    }

    if let Some(fix) = numer.to_fixnum_checked() {
        ctx.outputs[0] =
            unsafe { Value::from_fixnum(fix).as_handle_unchecked() };
    } else {
        ctx.outputs[0] = bool_object(ctx, false);
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
    if let (Some(numer), Some(denom)) = (
        value_to_i64(ratio.numerator),
        value_to_i64(ratio.denominator),
    ) {
        let numer = -(numer as i128);
        let denom = denom as i128;
        match make_ratio_from_i128s(ctx.heap, numer, denom, true) {
            Ok(res) => ctx.outputs[0] = res,
            Err(err) => return ExecutionResult::NumberError(err),
        }
        return ExecutionResult::Normal;
    }
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
    match make_ratio_from_bignums(ctx.heap, numer, denom, true) {
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
    let a_num_val = lhs.numerator;
    let a_den_val = lhs.denominator;
    let b_num_val = rhs.numerator;
    let b_den_val = rhs.denominator;

    if let (Some(a_num), Some(a_den), Some(b_num), Some(b_den)) = (
        value_to_i64(a_num_val),
        value_to_i64(a_den_val),
        value_to_i64(b_num_val),
        value_to_i64(b_den_val),
    ) {
        let numer = (a_num as i128) * (b_den as i128)
            + (b_num as i128) * (a_den as i128);
        let denom = (a_den as i128) * (b_den as i128);
        return make_ratio_from_i128s(heap, numer, denom, true);
    }

    let (a_num, a_den) = ratio_components_raw(heap, lhs)?;
    let (b_num, b_den) = ratio_components_raw(heap, rhs)?;

    let left = bignum_mul_raw(heap, &a_num, &b_den);
    let right = bignum_mul_raw(heap, &b_num, &a_den);
    let numer = bignum_add_raw(heap, &left, &right);
    let denom = bignum_mul_raw(heap, &a_den, &b_den);
    make_ratio_from_bignums(heap, numer, denom, true)
}

pub(crate) fn ratio_sub_raw(
    heap: &mut impl Allocator,
    lhs: Handle<Ratio>,
    rhs: Handle<Ratio>,
) -> Result<Handle<Value>, NumberError> {
    let a_num_val = lhs.numerator;
    let a_den_val = lhs.denominator;
    let b_num_val = rhs.numerator;
    let b_den_val = rhs.denominator;

    if let (Some(a_num), Some(a_den), Some(b_num), Some(b_den)) = (
        value_to_i64(a_num_val),
        value_to_i64(a_den_val),
        value_to_i64(b_num_val),
        value_to_i64(b_den_val),
    ) {
        let numer = (a_num as i128) * (b_den as i128)
            - (b_num as i128) * (a_den as i128);
        let denom = (a_den as i128) * (b_den as i128);
        return make_ratio_from_i128s(heap, numer, denom, true);
    }

    let (a_num, a_den) = ratio_components_raw(heap, lhs)?;
    let (b_num, b_den) = ratio_components_raw(heap, rhs)?;

    let left = bignum_mul_raw(heap, &a_num, &b_den);
    let right = bignum_mul_raw(heap, &b_num, &a_den);
    let numer = bignum_sub_raw(heap, &left, &right);
    let denom = bignum_mul_raw(heap, &a_den, &b_den);
    make_ratio_from_bignums(heap, numer, denom, true)
}

pub(crate) fn ratio_mul_raw(
    heap: &mut impl Allocator,
    lhs: Handle<Ratio>,
    rhs: Handle<Ratio>,
) -> Result<Handle<Value>, NumberError> {
    let a_num_val = lhs.numerator;
    let a_den_val = lhs.denominator;
    let b_num_val = rhs.numerator;
    let b_den_val = rhs.denominator;

    if let (Some(a_num), Some(a_den), Some(b_num), Some(b_den)) = (
        value_to_i64(a_num_val),
        value_to_i64(a_den_val),
        value_to_i64(b_num_val),
        value_to_i64(b_den_val),
    ) {
        let numer = (a_num as i128) * (b_num as i128);
        let denom = (a_den as i128) * (b_den as i128);
        return make_ratio_from_i128s(heap, numer, denom, true);
    }

    let (a_num, a_den) = ratio_components_raw(heap, lhs)?;
    let (b_num, b_den) = ratio_components_raw(heap, rhs)?;

    let numer = bignum_mul_raw(heap, &a_num, &b_num);
    let denom = bignum_mul_raw(heap, &a_den, &b_den);
    make_ratio_from_bignums(heap, numer, denom, true)
}

pub(crate) fn ratio_div_raw(
    heap: &mut impl Allocator,
    lhs: Handle<Ratio>,
    rhs: Handle<Ratio>,
) -> Result<Handle<Value>, NumberError> {
    let a_num_val = lhs.numerator;
    let a_den_val = lhs.denominator;
    let b_num_val = rhs.numerator;
    let b_den_val = rhs.denominator;

    if let (Some(a_num), Some(a_den), Some(b_num), Some(b_den)) = (
        value_to_i64(a_num_val),
        value_to_i64(a_den_val),
        value_to_i64(b_num_val),
        value_to_i64(b_den_val),
    ) {
        if b_num == 0 {
            return Err(NumberError::DivisionByZero);
        }
        let numer = (a_num as i128) * (b_den as i128);
        let denom = (a_den as i128) * (b_num as i128);
        return make_ratio_from_i128s(heap, numer, denom, true);
    }

    let (a_num, a_den) = ratio_components_raw(heap, lhs)?;
    let (b_num, b_den) = ratio_components_raw(heap, rhs)?;

    if is_bignum_zero(&b_num) {
        return Err(NumberError::DivisionByZero);
    }

    let numer = bignum_mul_raw(heap, &a_num, &b_den);
    let denom = bignum_mul_raw(heap, &a_den, &b_num);
    make_ratio_from_bignums(heap, numer, denom, true)
}

pub(crate) fn ratio_cmp_raw(
    heap: &mut impl Allocator,
    lhs: Handle<Ratio>,
    rhs: Handle<Ratio>,
) -> Result<std::cmp::Ordering, ExecutionResult> {
    let a_num_val = lhs.numerator;
    let a_den_val = lhs.denominator;
    let b_num_val = rhs.numerator;
    let b_den_val = rhs.denominator;

    if let (Some(a_num), Some(a_den), Some(b_num), Some(b_den)) = (
        value_to_i64(a_num_val),
        value_to_i64(a_den_val),
        value_to_i64(b_num_val),
        value_to_i64(b_den_val),
    ) {
        let left = (a_num as i128) * (b_den as i128);
        let right = (b_num as i128) * (a_den as i128);
        return Ok(left.cmp(&right));
    }

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
    if let (Some(numer), Some(denom)) = (
        value_to_i64(ratio.numerator),
        value_to_i64(ratio.denominator),
    ) {
        if denom == 0 {
            return ExecutionResult::NumberError(NumberError::DivisionByZero);
        }
        let res = (numer as f64) / (denom as f64);
        if !res.is_finite() {
            return ExecutionResult::Panic(
                "ratio>float: result not finite".to_string(),
            );
        }
        let float = ctx.heap.allocate_float(res);
        ctx.outputs[0] = float.into();
        return ExecutionResult::Normal;
    }
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
    if let (Some(numer), Some(denom)) = (
        value_to_i64(ratio.numerator),
        value_to_i64(ratio.denominator),
    ) {
        let mut out = String::new();
        out.push_str(&numer.to_string());
        out.push('/');
        out.push_str(&denom.to_string());

        let ba = ctx.heap.allocate_aligned_bytearray(out.as_bytes(), 8);
        let string = ctx.heap.allocate_string(ba);
        ctx.outputs[0] = string.into();
        return ExecutionResult::Normal;
    }
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
    use crate::{Allocator, Heap, HeapSettings, ObjectType, Value};

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
    fn ratio_mixed_components_adds() {
        let heap = Heap::new(HeapSettings::default());
        let mut heap = heap.proxy();

        // Use (1<<70) / 3 -- GCD is 1 (power of 2 vs 3), so it stays a ratio
        let big = heap.allocate_bignum_from_i128(1_i128 << 70);
        let a = make_ratio_from_values(
            &mut heap,
            big.into(),
            Value::from_fixnum(3),
        )
        .unwrap();
        let b = make_ratio_from_values(
            &mut heap,
            Value::from_fixnum(1),
            Value::from_fixnum(3),
        )
        .unwrap();

        // Verify a is a ratio (bignum numerator, fixnum denominator)
        let a_val = a.as_value();
        assert!(a_val.is_object());
        let a_ratio =
            unsafe { a_val.as_heap_handle_unchecked().cast::<crate::Ratio>() };

        let b_val = b.as_value();
        assert!(b_val.is_object());
        let b_ratio =
            unsafe { b_val.as_heap_handle_unchecked().cast::<crate::Ratio>() };

        // (1<<70)/3 + 1/3 = (1<<70 + 1)/3
        let result = ratio_add_raw(&mut heap, a_ratio, b_ratio).unwrap();
        let result_val = result.as_value();
        assert!(result_val.is_object());
        let handle = unsafe { result_val.as_heap_handle_unchecked() };
        assert_eq!(
            unsafe { handle.header.object_type().unwrap_unchecked() },
            ObjectType::Ratio
        );
        let ratio = unsafe { handle.cast::<crate::Ratio>() };

        assert_eq!(
            ratio
                .denominator
                .as_tagged_fixnum::<i64>()
                .unwrap()
                .as_i64(),
            3
        );
        // (1<<70 + 1) doesn't fit in i64, so numerator must be a bignum
        assert!(ratio.numerator.is_object());
        let handle = unsafe { ratio.numerator.as_heap_handle_unchecked() };
        assert_eq!(
            unsafe { handle.header.object_type().unwrap_unchecked() },
            ObjectType::BigNum
        );
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
