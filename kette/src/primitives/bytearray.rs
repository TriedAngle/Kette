use crate::{
    Allocator, ByteArray, ExecutionResult, ObjectType, PrimitiveContext, Value,
    primitives::inputs,
};
use std::ptr;

pub fn bytearray_print(ctx: &mut PrimitiveContext) -> ExecutionResult {
    // SAFETY: receiver must be valid Bytarray
    let ba = unsafe { ctx.receiver.cast::<ByteArray>() };
    let data = ba.as_bytes();
    let value = std::str::from_utf8(data).expect("valid utf8 encoding");
    
    if let Err(e) = write!(ctx.interpreter.output, "{}", value) {
        return ExecutionResult::Panic(format!("IO Error: {}", e));
    }
    
    ExecutionResult::Normal
}

pub fn bytearray_println(ctx: &mut PrimitiveContext) -> ExecutionResult {
    // SAFETY: receiver must be valid bytearray
    let ba = unsafe { ctx.receiver.cast::<ByteArray>() };
    let data = ba.as_bytes();
    let value = std::str::from_utf8(data).expect("valid utf8 encoding");

    if let Err(e) = writeln!(ctx.interpreter.output, "{}", value) {
        return ExecutionResult::Panic(format!("IO Error: {}", e));
    }

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
