use object::{ByteArray, Value};

use crate::alloc::alloc_byte_array;
use crate::interpreter::{with_roots, InterpreterState, RuntimeError};
use crate::primitives::string::alloc_vm_string_from_bytearray;
use crate::primitives::{expect_bytearray, expect_fixnum};
use crate::VM;

pub fn bytearray_size(
    _vm: &mut VM,
    _state: &mut InterpreterState,
    receiver: Value,
    _args: &[Value],
) -> Result<Value, RuntimeError> {
    let ptr = expect_bytearray(receiver)?;
    let len = unsafe { (*ptr).len() } as i64;
    Ok(Value::from_i64(len))
}

pub fn bytearray_clone_with_size(
    vm: &mut VM,
    state: &mut InterpreterState,
    _receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let size_val = args.get(0).copied().ok_or(RuntimeError::TypeError {
        expected: "size",
        got: Value::from_i64(0),
    })?;
    let size = expect_fixnum(size_val)?;
    if size < 0 {
        return Err(RuntimeError::Unimplemented {
            message: "bytearray size must be non-negative",
        });
    }
    let len = size as usize;
    let bytes = vec![0u8; len];
    let mut scratch = Vec::new();
    let ba = with_roots(vm, state, &mut scratch, |proxy, roots| unsafe {
        alloc_byte_array(proxy, roots, &bytes).value()
    });
    Ok(ba)
}

pub fn bytearray_memcopy(
    _vm: &mut VM,
    _state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    memcopy(receiver, args, false)
}

pub fn bytearray_memcopy_overlapping(
    _vm: &mut VM,
    _state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    memcopy(receiver, args, true)
}

pub fn bytearray_to_string(
    vm: &mut VM,
    state: &mut InterpreterState,
    receiver: Value,
    _args: &[Value],
) -> Result<Value, RuntimeError> {
    let ba = expect_bytearray(receiver)?;
    let len = unsafe { (*ba).len() } as usize;
    if len == 0 {
        return Ok(vm.special.none);
    }
    let bytes = unsafe { (*ba).bytes() };
    if *bytes.last().unwrap() != 0 {
        return Ok(vm.special.none);
    }
    let content = &bytes[..len - 1];
    if std::str::from_utf8(content).is_err() {
        return Ok(vm.special.none);
    }
    let result =
        alloc_vm_string_from_bytearray(vm, state, receiver, (len - 1) as u64)?;
    Ok(result)
}

fn memcopy(
    receiver: Value,
    args: &[Value],
    allow_overlap: bool,
) -> Result<Value, RuntimeError> {
    let src = args.get(0).copied().ok_or(RuntimeError::TypeError {
        expected: "source",
        got: Value::from_i64(0),
    })?;
    let src_offset_val =
        args.get(1).copied().ok_or(RuntimeError::TypeError {
            expected: "source offset",
            got: Value::from_i64(0),
        })?;
    let dst_offset_val =
        args.get(2).copied().ok_or(RuntimeError::TypeError {
            expected: "destination offset",
            got: Value::from_i64(0),
        })?;
    let len_val = args.get(3).copied().ok_or(RuntimeError::TypeError {
        expected: "length",
        got: Value::from_i64(0),
    })?;

    let src_offset = expect_fixnum(src_offset_val)?;
    let dst_offset = expect_fixnum(dst_offset_val)?;
    let len = expect_fixnum(len_val)?;
    if src_offset < 0 || dst_offset < 0 || len < 0 {
        return Err(RuntimeError::Unimplemented {
            message: "bytearray offsets must be non-negative",
        });
    }

    let src_ptr = expect_bytearray(src)? as *const ByteArray;
    let dst_ptr = expect_bytearray(receiver)? as *mut ByteArray;
    let src_len = unsafe { (*src_ptr).len() } as i64;
    let dst_len = unsafe { (*dst_ptr).len() } as i64;
    if src_offset + len > src_len || dst_offset + len > dst_len {
        return Err(RuntimeError::Unimplemented {
            message: "bytearray copy out of bounds",
        });
    }

    if len == 0 {
        return Ok(receiver);
    }

    let src_off = src_offset as usize;
    let dst_off = dst_offset as usize;
    let count = len as usize;

    if src.raw() == receiver.raw() {
        let src_end = src_off + count;
        let dst_end = dst_off + count;
        if src_off < dst_end && dst_off < src_end {
            if !allow_overlap {
                return Err(RuntimeError::Unimplemented {
                    message: "bytearray copy overlap",
                });
            }
        }
    }

    unsafe {
        let base = dst_ptr.add(1) as *mut u8;
        let dst_bytes = base.add(dst_off);
        let src_bytes = (src_ptr.add(1) as *const u8).add(src_off);
        if allow_overlap {
            std::ptr::copy(src_bytes, dst_bytes, count);
        } else {
            std::ptr::copy_nonoverlapping(src_bytes, dst_bytes, count);
        }
    }

    Ok(receiver)
}
