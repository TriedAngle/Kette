use crate::{
    primitives::inputs, Alien, Allocator, ExecutionResult, PrimitiveContext,
    Value,
};

const FIXNUM_MIN: i64 = -(1_i64 << 62);
const FIXNUM_MAX: i64 = (1_i64 << 62) - 1;

fn output_i64(ctx: &mut PrimitiveContext, value: i64) -> ExecutionResult {
    if value < FIXNUM_MIN || value > FIXNUM_MAX {
        let big = ctx.heap.allocate_bignum_from_i64(value);
        ctx.outputs[0] = big.into();
        return ExecutionResult::Normal;
    }
    ctx.outputs[0] = unsafe { Value::from_fixnum(value).as_handle_unchecked() };
    ExecutionResult::Normal
}

fn output_u64(ctx: &mut PrimitiveContext, value: u64) -> ExecutionResult {
    if value > FIXNUM_MAX as u64 {
        let big = ctx.heap.allocate_bignum_from_u64(value);
        ctx.outputs[0] = big.into();
        return ExecutionResult::Normal;
    }
    ctx.outputs[0] = unsafe { Value::from_u64(value).as_handle_unchecked() };
    ExecutionResult::Normal
}

fn index_from_fixnum(
    value: crate::Handle<Value>,
    name: &str,
) -> Result<usize, ExecutionResult> {
    if !value.is_fixnum() {
        return Err(ExecutionResult::Panic(format!(
            "{name}: index must be a fixnum"
        )));
    }
    let idx = unsafe { value.as_fixnum::<i64>() };
    if idx < 0 {
        return Err(ExecutionResult::Panic(format!(
            "{name}: index must be >= 0"
        )));
    }
    Ok(idx as usize)
}

fn alien_ptr(ctx: &PrimitiveContext) -> Result<*mut u8, ExecutionResult> {
    // SAFETY: receiver must be valid Alien
    let alien = unsafe { ctx.receiver.cast::<Alien>() };
    let ptr_value: usize = alien.ptr.into();
    let ptr = ptr_value as *mut u8;
    if ptr.is_null() {
        return Err(ExecutionResult::Panic(
            "alien pointer is null".to_string(),
        ));
    }
    Ok(ptr)
}

fn read_unaligned<T: Copy>(ptr: *const u8) -> T {
    // SAFETY: caller validates pointer
    unsafe { (ptr as *const T).read_unaligned() }
}

fn write_unaligned<T>(ptr: *mut u8, value: T) {
    // SAFETY: caller validates pointer
    unsafe { (ptr as *mut T).write_unaligned(value) };
}

fn get_fixnum_i64(
    value: crate::Handle<Value>,
    name: &str,
) -> Result<i64, ExecutionResult> {
    if !value.is_fixnum() {
        return Err(ExecutionResult::Panic(format!(
            "{name}: value must be a fixnum"
        )));
    }
    Ok(unsafe { value.as_fixnum::<i64>() })
}

fn check_signed_range(
    value: i64,
    min: i64,
    max: i64,
    name: &str,
) -> Result<i64, ExecutionResult> {
    if value < min || value > max {
        return Err(ExecutionResult::Panic(format!(
            "{name}: value out of range"
        )));
    }
    Ok(value)
}

fn check_unsigned_range(
    value: i64,
    max: u64,
    name: &str,
) -> Result<u64, ExecutionResult> {
    if value < 0 || (value as u64) > max {
        return Err(ExecutionResult::Panic(format!(
            "{name}: value out of range"
        )));
    }
    Ok(value as u64)
}

pub fn alien_u8_at(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let [index_val] = inputs(ctx);
    let index = match index_from_fixnum(index_val, "alienU8At") {
        Ok(value) => value,
        Err(err) => return err,
    };
    let ptr = match alien_ptr(ctx) {
        Ok(ptr) => ptr,
        Err(err) => return err,
    };
    let value: u8 = read_unaligned(ptr.wrapping_add(index));
    output_u64(ctx, value as u64)
}

pub fn alien_i8_at(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let [index_val] = inputs(ctx);
    let index = match index_from_fixnum(index_val, "alienI8At") {
        Ok(value) => value,
        Err(err) => return err,
    };
    let ptr = match alien_ptr(ctx) {
        Ok(ptr) => ptr,
        Err(err) => return err,
    };
    let value: i8 = read_unaligned(ptr.wrapping_add(index));
    output_i64(ctx, value as i64)
}

pub fn alien_u16_at(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let [index_val] = inputs(ctx);
    let index = match index_from_fixnum(index_val, "alienU16At") {
        Ok(value) => value,
        Err(err) => return err,
    };
    let ptr = match alien_ptr(ctx) {
        Ok(ptr) => ptr,
        Err(err) => return err,
    };
    let value: u16 = read_unaligned(ptr.wrapping_add(index));
    output_u64(ctx, value as u64)
}

pub fn alien_i16_at(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let [index_val] = inputs(ctx);
    let index = match index_from_fixnum(index_val, "alienI16At") {
        Ok(value) => value,
        Err(err) => return err,
    };
    let ptr = match alien_ptr(ctx) {
        Ok(ptr) => ptr,
        Err(err) => return err,
    };
    let value: i16 = read_unaligned(ptr.wrapping_add(index));
    output_i64(ctx, value as i64)
}

pub fn alien_u32_at(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let [index_val] = inputs(ctx);
    let index = match index_from_fixnum(index_val, "alienU32At") {
        Ok(value) => value,
        Err(err) => return err,
    };
    let ptr = match alien_ptr(ctx) {
        Ok(ptr) => ptr,
        Err(err) => return err,
    };
    let value: u32 = read_unaligned(ptr.wrapping_add(index));
    output_u64(ctx, value as u64)
}

pub fn alien_i32_at(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let [index_val] = inputs(ctx);
    let index = match index_from_fixnum(index_val, "alienI32At") {
        Ok(value) => value,
        Err(err) => return err,
    };
    let ptr = match alien_ptr(ctx) {
        Ok(ptr) => ptr,
        Err(err) => return err,
    };
    let value: i32 = read_unaligned(ptr.wrapping_add(index));
    output_i64(ctx, value as i64)
}

pub fn alien_u64_at(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let [index_val] = inputs(ctx);
    let index = match index_from_fixnum(index_val, "alienU64At") {
        Ok(value) => value,
        Err(err) => return err,
    };
    let ptr = match alien_ptr(ctx) {
        Ok(ptr) => ptr,
        Err(err) => return err,
    };
    let value: u64 = read_unaligned(ptr.wrapping_add(index));
    output_u64(ctx, value)
}

pub fn alien_i64_at(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let [index_val] = inputs(ctx);
    let index = match index_from_fixnum(index_val, "alienI64At") {
        Ok(value) => value,
        Err(err) => return err,
    };
    let ptr = match alien_ptr(ctx) {
        Ok(ptr) => ptr,
        Err(err) => return err,
    };
    let value: i64 = read_unaligned(ptr.wrapping_add(index));
    output_i64(ctx, value)
}

pub fn alien_u8_at_put(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let [index_val, value_val] = inputs(ctx);
    let index = match index_from_fixnum(index_val, "alienU8AtPut") {
        Ok(value) => value,
        Err(err) => return err,
    };
    let value = match get_fixnum_i64(value_val, "alienU8AtPut") {
        Ok(value) => value,
        Err(err) => return err,
    };
    let value =
        match check_unsigned_range(value, u8::MAX as u64, "alienU8AtPut") {
            Ok(value) => value as u8,
            Err(err) => return err,
        };
    let ptr = match alien_ptr(ctx) {
        Ok(ptr) => ptr,
        Err(err) => return err,
    };
    write_unaligned(ptr.wrapping_add(index), value);
    ExecutionResult::Normal
}

pub fn alien_i8_at_put(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let [index_val, value_val] = inputs(ctx);
    let index = match index_from_fixnum(index_val, "alienI8AtPut") {
        Ok(value) => value,
        Err(err) => return err,
    };
    let value = match get_fixnum_i64(value_val, "alienI8AtPut") {
        Ok(value) => value,
        Err(err) => return err,
    };
    let value = match check_signed_range(
        value,
        i8::MIN as i64,
        i8::MAX as i64,
        "alienI8AtPut",
    ) {
        Ok(value) => value as i8,
        Err(err) => return err,
    };
    let ptr = match alien_ptr(ctx) {
        Ok(ptr) => ptr,
        Err(err) => return err,
    };
    write_unaligned(ptr.wrapping_add(index), value);
    ExecutionResult::Normal
}

pub fn alien_u16_at_put(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let [index_val, value_val] = inputs(ctx);
    let index = match index_from_fixnum(index_val, "alienU16AtPut") {
        Ok(value) => value,
        Err(err) => return err,
    };
    let value = match get_fixnum_i64(value_val, "alienU16AtPut") {
        Ok(value) => value,
        Err(err) => return err,
    };
    let value =
        match check_unsigned_range(value, u16::MAX as u64, "alienU16AtPut") {
            Ok(value) => value as u16,
            Err(err) => return err,
        };
    let ptr = match alien_ptr(ctx) {
        Ok(ptr) => ptr,
        Err(err) => return err,
    };
    write_unaligned(ptr.wrapping_add(index), value);
    ExecutionResult::Normal
}

pub fn alien_i16_at_put(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let [index_val, value_val] = inputs(ctx);
    let index = match index_from_fixnum(index_val, "alienI16AtPut") {
        Ok(value) => value,
        Err(err) => return err,
    };
    let value = match get_fixnum_i64(value_val, "alienI16AtPut") {
        Ok(value) => value,
        Err(err) => return err,
    };
    let value = match check_signed_range(
        value,
        i16::MIN as i64,
        i16::MAX as i64,
        "alienI16AtPut",
    ) {
        Ok(value) => value as i16,
        Err(err) => return err,
    };
    let ptr = match alien_ptr(ctx) {
        Ok(ptr) => ptr,
        Err(err) => return err,
    };
    write_unaligned(ptr.wrapping_add(index), value);
    ExecutionResult::Normal
}

pub fn alien_u32_at_put(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let [index_val, value_val] = inputs(ctx);
    let index = match index_from_fixnum(index_val, "alienU32AtPut") {
        Ok(value) => value,
        Err(err) => return err,
    };
    let value = match get_fixnum_i64(value_val, "alienU32AtPut") {
        Ok(value) => value,
        Err(err) => return err,
    };
    let value =
        match check_unsigned_range(value, u32::MAX as u64, "alienU32AtPut") {
            Ok(value) => value as u32,
            Err(err) => return err,
        };
    let ptr = match alien_ptr(ctx) {
        Ok(ptr) => ptr,
        Err(err) => return err,
    };
    write_unaligned(ptr.wrapping_add(index), value);
    ExecutionResult::Normal
}

pub fn alien_i32_at_put(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let [index_val, value_val] = inputs(ctx);
    let index = match index_from_fixnum(index_val, "alienI32AtPut") {
        Ok(value) => value,
        Err(err) => return err,
    };
    let value = match get_fixnum_i64(value_val, "alienI32AtPut") {
        Ok(value) => value,
        Err(err) => return err,
    };
    let value = match check_signed_range(
        value,
        i32::MIN as i64,
        i32::MAX as i64,
        "alienI32AtPut",
    ) {
        Ok(value) => value as i32,
        Err(err) => return err,
    };
    let ptr = match alien_ptr(ctx) {
        Ok(ptr) => ptr,
        Err(err) => return err,
    };
    write_unaligned(ptr.wrapping_add(index), value);
    ExecutionResult::Normal
}

pub fn alien_u64_at_put(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let [index_val, value_val] = inputs(ctx);
    let index = match index_from_fixnum(index_val, "alienU64AtPut") {
        Ok(value) => value,
        Err(err) => return err,
    };
    let value = match get_fixnum_i64(value_val, "alienU64AtPut") {
        Ok(value) => value,
        Err(err) => return err,
    };
    let value = match check_unsigned_range(value, u64::MAX, "alienU64AtPut") {
        Ok(value) => value as u64,
        Err(err) => return err,
    };
    let ptr = match alien_ptr(ctx) {
        Ok(ptr) => ptr,
        Err(err) => return err,
    };
    write_unaligned(ptr.wrapping_add(index), value);
    ExecutionResult::Normal
}

pub fn alien_i64_at_put(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let [index_val, value_val] = inputs(ctx);
    let index = match index_from_fixnum(index_val, "alienI64AtPut") {
        Ok(value) => value,
        Err(err) => return err,
    };
    let value = match get_fixnum_i64(value_val, "alienI64AtPut") {
        Ok(value) => value,
        Err(err) => return err,
    };
    let value =
        match check_signed_range(value, i64::MIN, i64::MAX, "alienI64AtPut") {
            Ok(value) => value,
            Err(err) => return err,
        };
    let ptr = match alien_ptr(ctx) {
        Ok(ptr) => ptr,
        Err(err) => return err,
    };
    write_unaligned(ptr.wrapping_add(index), value);
    ExecutionResult::Normal
}
