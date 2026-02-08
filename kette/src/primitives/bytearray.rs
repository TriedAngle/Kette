use crate::{
    Allocator, ByteArray, ExecutionResult, ObjectType, PrimitiveContext,
    StringObject, Value, primitives::inputs,
};
use std::{mem, ptr};

pub fn bytearray_print(ctx: &mut PrimitiveContext) -> ExecutionResult {
    // SAFETY: receiver must be valid bytearray or string
    match unsafe { ctx.receiver.as_heap_value_handle() }
        .header
        .object_type()
    {
        Some(ObjectType::ByteArray) => {
            let ba = unsafe { ctx.receiver.cast::<ByteArray>() };
            let data = ba.as_bytes();
            let value = std::str::from_utf8(data).expect("valid utf8 encoding");
            if let Err(e) = write!(ctx.interpreter.output, "{}", value) {
                return ExecutionResult::Panic(format!("IO Error: {}", e));
            }
        }
        Some(ObjectType::String) => {
            let s = unsafe { ctx.receiver.cast::<StringObject>() };
            let value = s.as_utf8().expect("valid utf8 encoding");
            if let Err(e) = write!(ctx.interpreter.output, "{}", value) {
                return ExecutionResult::Panic(format!("IO Error: {}", e));
            }
        }
        _ => {
            return ExecutionResult::Panic(
                "(print): receiver must be bytearray or string".to_string(),
            );
        }
    };

    ExecutionResult::Normal
}

pub fn bytearray_println(ctx: &mut PrimitiveContext) -> ExecutionResult {
    // SAFETY: receiver must be valid bytearray or string
    match unsafe { ctx.receiver.as_heap_value_handle() }
        .header
        .object_type()
    {
        Some(ObjectType::ByteArray) => {
            let ba = unsafe { ctx.receiver.cast::<ByteArray>() };
            let data = ba.as_bytes();
            let value = std::str::from_utf8(data).expect("valid utf8 encoding");
            if let Err(e) = writeln!(ctx.interpreter.output, "{}", value) {
                return ExecutionResult::Panic(format!("IO Error: {}", e));
            }
        }
        Some(ObjectType::String) => {
            let s = unsafe { ctx.receiver.cast::<StringObject>() };
            let value = s.as_utf8().expect("valid utf8 encoding");
            if let Err(e) = writeln!(ctx.interpreter.output, "{}", value) {
                return ExecutionResult::Panic(format!("IO Error: {}", e));
            }
        }
        _ => {
            return ExecutionResult::Panic(
                "(println): receiver must be bytearray or string".to_string(),
            );
        }
    };

    ExecutionResult::Normal
}

pub fn parent(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let p = ctx.vm.specials().bytearray_traits;
    ctx.outputs[0] = p.into();
    ExecutionResult::Normal
}

pub fn size(ctx: &mut PrimitiveContext) -> ExecutionResult {
    // SAFETY: safe by contract
    let ba = unsafe { ctx.receiver.cast::<ByteArray>() };
    ctx.outputs[0] = ba.size.into();
    ExecutionResult::Normal
}

pub fn bytearray_new(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let [size_val] = inputs(ctx);

    if !size_val.is_fixnum() {
        return ExecutionResult::Panic(
            "bytearrayNew: size must be a fixnum".to_string(),
        );
    }

    // SAFETY: safe if contract holds
    let size = unsafe { size_val.as_fixnum::<usize>() };

    // allocate_bytearray inside heap.rs calls init_zeroed internally,
    // which uses ptr::write_bytes to zero the memory.
    let ba = ctx.heap.allocate_aligned_bytearray_zeroed(size, 8);

    ctx.outputs[0] = ba.into();
    ExecutionResult::Normal
}

// ( index -- value ) | rec: ba
pub fn bytearray_at(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let [index_val] = inputs(ctx);
    // SAFETY: safe if contract holds
    let ba = unsafe { ctx.receiver.cast::<ByteArray>() };

    if !index_val.is_fixnum() {
        return ExecutionResult::Panic(
            "bytearrayAt: index must be a fixnum".to_string(),
        );
    }

    // SAFETY: safe if contract holds
    let index = unsafe { index_val.as_fixnum::<usize>() };
    let slice = ba.inner().as_bytes();

    if index >= slice.len() {
        return ExecutionResult::Panic(
            "bytearrayAt: index out of bounds".to_string(),
        );
    }

    let val = slice[index];
    // SAFETY: this is safe
    ctx.outputs[0] =
        unsafe { Value::from_fixnum(val as i64).as_handle_unchecked() };
    ExecutionResult::Normal
}

// ( value index -- ) | rec: barray
pub fn bytearray_at_put(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let [index_val, value_val] = crate::primitives::inputs(ctx);
    // SAFETY: safe if contract holds
    let mut ba = unsafe { ctx.receiver.cast::<ByteArray>() };

    if !index_val.is_fixnum() || !value_val.is_fixnum() {
        return ExecutionResult::Panic(
            "bytearrayAtPut: index and value must be fixnums".to_string(),
        );
    }

    // SAFETY: safe if contract holds
    let index = unsafe { index_val.as_fixnum::<usize>() };
    // SAFETY: safe if contract holds
    let value = unsafe { value_val.as_fixnum::<usize>() as u8 }; // truncates higher bits

    let slice = ba.as_bytes_mut();

    if index >= slice.len() {
        return ExecutionResult::Panic(
            "bytearrayAtPut: index out of bounds".to_string(),
        );
    }

    slice[index] = value;

    ExecutionResult::Normal
}

// ( index count value -- ) | rec: ba
pub fn bytearray_memset(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let [index_v, count_v, value_v] = crate::primitives::inputs(ctx);
    // SAFETY: safe if contract holds
    let mut ba = unsafe { ctx.receiver.cast::<ByteArray>() };

    if !index_v.is_fixnum() || !count_v.is_fixnum() || !value_v.is_fixnum() {
        return ExecutionResult::Panic(
            "bytearrayMemset: args must be fixnums".to_string(),
        );
    }

    // SAFETY: safe if contract holds
    let start = unsafe { index_v.as_fixnum::<usize>() };
    // SAFETY: safe if contract holds
    let count = unsafe { count_v.as_fixnum::<usize>() };
    // SAFETY: safe if contract holds
    let value = unsafe { value_v.as_fixnum::<usize>() as u8 };

    let slice = ba.as_bytes_mut();

    if start + count > slice.len() {
        return ExecutionResult::Panic(
            "bytearrayMemset: range out of bounds".to_string(),
        );
    }

    // SAFETY: checked
    unsafe {
        ptr::write_bytes(slice.as_mut_ptr().add(start), value, count);
    }

    ExecutionResult::Normal
}

// ( selfOffset source sourceOffset byteCount -- ) | rec: dest
pub fn bytearray_memcpy(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let [dest_idx_v, src_obj_v, src_idx_v, count_v] = inputs(ctx);

    // SAFETY: safe if contract holds
    let mut dest = unsafe { ctx.receiver.cast::<ByteArray>() };

    if !dest_idx_v.is_fixnum() || !src_idx_v.is_fixnum() || !count_v.is_fixnum()
    {
        return ExecutionResult::Panic(
            "bytearrayMemcpy: indices/count must be fixnums".to_string(),
        );
    }

    // SAFETY: checked
    let src_handle = unsafe { src_obj_v.as_heap_value_handle() };
    if src_handle.header.object_type() != Some(ObjectType::ByteArray) {
        return ExecutionResult::Panic(
            "bytearrayMemcpy: source must be a bytearray".to_string(),
        );
    }
    // SAFETY: safe if contract holds
    let src = unsafe { src_handle.cast::<ByteArray>() };

    // SAFETY: safe if contract holds
    let dest_start = unsafe { dest_idx_v.as_fixnum::<usize>() };
    // SAFETY: safe if contract holds
    let src_start = unsafe { src_idx_v.as_fixnum::<usize>() };
    // SAFETY: safe if contract holds
    let count = unsafe { count_v.as_fixnum::<usize>() };

    let dest_slice = dest.as_bytes_mut();
    let src_slice = src.as_bytes();

    if dest_start + count > dest_slice.len()
        || src_start + count > src_slice.len()
    {
        return ExecutionResult::Panic(
            "bytearrayMemcpy: range out of bounds".to_string(),
        );
    }

    // SAFETY: checked
    unsafe {
        ptr::copy_nonoverlapping(
            src_slice.as_ptr().add(src_start),
            dest_slice.as_mut_ptr().add(dest_start),
            count,
        );
    }

    ExecutionResult::Normal
}

pub fn bytearray_to_string(ctx: &mut PrimitiveContext) -> ExecutionResult {
    // SAFETY: receiver must be valid bytearray
    let ba = unsafe { ctx.receiver.cast::<ByteArray>() };
    let data = ba.as_bytes();
    if std::str::from_utf8(data).is_err() {
        return ExecutionResult::Panic(
            "bytearray>string: bytearray must be valid utf8".to_string(),
        );
    }

    let string = ctx.heap.allocate_string(ba);
    ctx.outputs[0] = string.into();
    ExecutionResult::Normal
}

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

fn read_unaligned<T: Copy>(ptr: *const u8) -> T {
    // SAFETY: caller validates pointer range
    unsafe { (ptr as *const T).read_unaligned() }
}

fn write_unaligned<T>(ptr: *mut u8, value: T) {
    // SAFETY: caller validates pointer range
    unsafe { (ptr as *mut T).write_unaligned(value) };
}

fn bytearray_read<T: Copy>(
    ctx: &mut PrimitiveContext,
    name: &str,
) -> Result<T, ExecutionResult> {
    let [index_val] = inputs(ctx);
    let index = index_from_fixnum(index_val, name)?;
    let ba = unsafe { ctx.receiver.cast::<ByteArray>() };
    let size = mem::size_of::<T>();
    let slice = ba.as_bytes();
    if index
        .checked_add(size)
        .map_or(true, |end| end > slice.len())
    {
        return Err(ExecutionResult::Panic(format!(
            "{name}: index out of bounds"
        )));
    }
    let ptr = unsafe { slice.as_ptr().add(index) };
    let value: T = read_unaligned(ptr);
    Ok(value)
}

fn bytearray_write<T>(
    ctx: &mut PrimitiveContext,
    name: &str,
) -> Result<(*mut u8, i64), ExecutionResult> {
    let [index_val, value_val] = inputs(ctx);
    let index = index_from_fixnum(index_val, name)?;
    let value = get_fixnum_i64(value_val, name)?;
    let mut ba = unsafe { ctx.receiver.cast::<ByteArray>() };
    let size = mem::size_of::<T>();
    let slice = ba.as_bytes_mut();
    if index
        .checked_add(size)
        .map_or(true, |end| end > slice.len())
    {
        return Err(ExecutionResult::Panic(format!(
            "{name}: index out of bounds"
        )));
    }
    let ptr = unsafe { slice.as_mut_ptr().add(index) };
    Ok((ptr, value))
}

pub fn bytearray_u16_at(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let value = match bytearray_read::<u16>(ctx, "bytearrayU16At") {
        Ok(value) => value,
        Err(err) => return err,
    };
    output_u64(ctx, value as u64)
}

pub fn bytearray_i16_at(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let value = match bytearray_read::<i16>(ctx, "bytearrayI16At") {
        Ok(value) => value,
        Err(err) => return err,
    };
    output_i64(ctx, value as i64)
}

pub fn bytearray_u32_at(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let value = match bytearray_read::<u32>(ctx, "bytearrayU32At") {
        Ok(value) => value,
        Err(err) => return err,
    };
    output_u64(ctx, value as u64)
}

pub fn bytearray_i32_at(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let value = match bytearray_read::<i32>(ctx, "bytearrayI32At") {
        Ok(value) => value,
        Err(err) => return err,
    };
    output_i64(ctx, value as i64)
}

pub fn bytearray_u64_at(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let value = match bytearray_read::<u64>(ctx, "bytearrayU64At") {
        Ok(value) => value,
        Err(err) => return err,
    };
    output_u64(ctx, value)
}

pub fn bytearray_i64_at(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let value = match bytearray_read::<i64>(ctx, "bytearrayI64At") {
        Ok(value) => value,
        Err(err) => return err,
    };
    output_i64(ctx, value)
}

pub fn bytearray_u16_at_put(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let (ptr, value) = match bytearray_write::<u16>(ctx, "bytearrayU16AtPut") {
        Ok(value) => value,
        Err(err) => return err,
    };
    let value =
        match check_unsigned_range(value, u16::MAX as u64, "bytearrayU16AtPut")
        {
            Ok(value) => value as u16,
            Err(err) => return err,
        };
    write_unaligned(ptr, value);
    ExecutionResult::Normal
}

pub fn bytearray_i16_at_put(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let (ptr, value) = match bytearray_write::<i16>(ctx, "bytearrayI16AtPut") {
        Ok(value) => value,
        Err(err) => return err,
    };
    let value = match check_signed_range(
        value,
        i16::MIN as i64,
        i16::MAX as i64,
        "bytearrayI16AtPut",
    ) {
        Ok(value) => value as i16,
        Err(err) => return err,
    };
    write_unaligned(ptr, value);
    ExecutionResult::Normal
}

pub fn bytearray_u32_at_put(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let (ptr, value) = match bytearray_write::<u32>(ctx, "bytearrayU32AtPut") {
        Ok(value) => value,
        Err(err) => return err,
    };
    let value =
        match check_unsigned_range(value, u32::MAX as u64, "bytearrayU32AtPut")
        {
            Ok(value) => value as u32,
            Err(err) => return err,
        };
    write_unaligned(ptr, value);
    ExecutionResult::Normal
}

pub fn bytearray_i32_at_put(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let (ptr, value) = match bytearray_write::<i32>(ctx, "bytearrayI32AtPut") {
        Ok(value) => value,
        Err(err) => return err,
    };
    let value = match check_signed_range(
        value,
        i32::MIN as i64,
        i32::MAX as i64,
        "bytearrayI32AtPut",
    ) {
        Ok(value) => value as i32,
        Err(err) => return err,
    };
    write_unaligned(ptr, value);
    ExecutionResult::Normal
}

pub fn bytearray_u64_at_put(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let (ptr, value) = match bytearray_write::<u64>(ctx, "bytearrayU64AtPut") {
        Ok(value) => value,
        Err(err) => return err,
    };
    let value = match check_unsigned_range(value, u64::MAX, "bytearrayU64AtPut")
    {
        Ok(value) => value as u64,
        Err(err) => return err,
    };
    write_unaligned(ptr, value);
    ExecutionResult::Normal
}

pub fn bytearray_i64_at_put(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let (ptr, value) = match bytearray_write::<i64>(ctx, "bytearrayI64AtPut") {
        Ok(value) => value,
        Err(err) => return err,
    };
    let value = match check_signed_range(
        value,
        i64::MIN,
        i64::MAX,
        "bytearrayI64AtPut",
    ) {
        Ok(value) => value,
        Err(err) => return err,
    };
    write_unaligned(ptr, value);
    ExecutionResult::Normal
}
