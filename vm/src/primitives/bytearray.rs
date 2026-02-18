use std::mem::size_of;

use object::{ByteArray, Value};

use crate::alloc::{
    alloc_alien, alloc_bignum_from_i128, alloc_byte_array, alloc_float,
};
use crate::interpreter::{with_roots, InterpreterState, RuntimeError};
use crate::primitives::string::alloc_vm_string_from_bytearray;
use crate::primitives::{
    expect_alien, expect_bignum, expect_bytearray, expect_fixnum, expect_float,
};
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

fn output_i64(
    vm: &mut VM,
    state: &mut InterpreterState,
    roots: &mut Vec<Value>,
    value: i64,
) -> Value {
    if (-((1_i64) << 62)..=((1_i64 << 62) - 1)).contains(&value) {
        return Value::from_i64(value);
    }
    with_roots(vm, state, roots, |proxy, root_provider| unsafe {
        alloc_bignum_from_i128(proxy, root_provider, value as i128).value()
    })
}

fn output_u64(
    vm: &mut VM,
    state: &mut InterpreterState,
    roots: &mut Vec<Value>,
    value: u64,
) -> Value {
    if value <= object::BigNum::FIXNUM_MAX as u64 {
        return Value::from_i64(value as i64);
    }
    with_roots(vm, state, roots, |proxy, root_provider| unsafe {
        alloc_bignum_from_i128(proxy, root_provider, value as i128).value()
    })
}

fn value_to_i64(value: Value) -> Result<i64, RuntimeError> {
    if value.is_fixnum() {
        return expect_fixnum(value);
    }
    let bn_ptr = expect_bignum(value)?;
    let bn = unsafe { &*bn_ptr };
    match (bn.sign, bn.len()) {
        (0, _) => Ok(0),
        (1, 1) => {
            let limb = bn.limbs()[0];
            if limb <= i64::MAX as u64 {
                Ok(limb as i64)
            } else {
                Err(RuntimeError::Unimplemented {
                    message: "integer out of i64 range",
                })
            }
        }
        (-1, 1) => {
            let limb = bn.limbs()[0];
            if limb == (1_u64 << 63) {
                Ok(i64::MIN)
            } else if limb < (1_u64 << 63) {
                Ok(-(limb as i64))
            } else {
                Err(RuntimeError::Unimplemented {
                    message: "integer out of i64 range",
                })
            }
        }
        _ => Err(RuntimeError::Unimplemented {
            message: "integer out of i64 range",
        }),
    }
}

fn value_to_u64(value: Value) -> Result<u64, RuntimeError> {
    if value.is_fixnum() {
        let n = expect_fixnum(value)?;
        if n < 0 {
            return Err(RuntimeError::Unimplemented {
                message: "integer out of u64 range",
            });
        }
        return Ok(n as u64);
    }
    let bn_ptr = expect_bignum(value)?;
    let bn = unsafe { &*bn_ptr };
    match (bn.sign, bn.len()) {
        (0, _) => Ok(0),
        (1, 1) => Ok(bn.limbs()[0]),
        _ => Err(RuntimeError::Unimplemented {
            message: "integer out of u64 range",
        }),
    }
}

fn bounds_checked_ptr(
    receiver: Value,
    offset: i64,
    elem_size: usize,
) -> Result<*mut u8, RuntimeError> {
    if offset < 0 {
        return Err(RuntimeError::Unimplemented {
            message: "bytearray index must be non-negative",
        });
    }
    let ptr = expect_bytearray(receiver)? as *mut ByteArray;
    let len = unsafe { (*ptr).len() } as usize;
    let off = offset as usize;
    if off.checked_add(elem_size).is_none() || off + elem_size > len {
        return Err(RuntimeError::Unimplemented {
            message: "bytearray index out of bounds",
        });
    }
    Ok(unsafe { (ptr.add(1) as *mut u8).add(off) })
}

macro_rules! bytearray_read_int {
    ($name:ident, $ty:ty) => {
        pub fn $name(
            _vm: &mut VM,
            _state: &mut InterpreterState,
            receiver: Value,
            args: &[Value],
        ) -> Result<Value, RuntimeError> {
            let idx_v =
                args.get(0).copied().ok_or(RuntimeError::TypeError {
                    expected: "index",
                    got: Value::from_i64(0),
                })?;
            let index = expect_fixnum(idx_v)?;
            let p = bounds_checked_ptr(receiver, index, size_of::<$ty>())?;
            let value = unsafe { (p as *const $ty).read_unaligned() } as i64;
            Ok(Value::from_i64(value))
        }
    };
}

bytearray_read_int!(bytearray_read_u8, u8);
bytearray_read_int!(bytearray_read_i8, i8);
bytearray_read_int!(bytearray_read_u16, u16);
bytearray_read_int!(bytearray_read_i16, i16);
bytearray_read_int!(bytearray_read_u32, u32);
bytearray_read_int!(bytearray_read_i32, i32);

pub fn bytearray_read_u64(
    vm: &mut VM,
    state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let idx_v = args.get(0).copied().ok_or(RuntimeError::TypeError {
        expected: "index",
        got: Value::from_i64(0),
    })?;
    let index = expect_fixnum(idx_v)?;
    let p = bounds_checked_ptr(receiver, index, size_of::<u64>())?;
    let value = unsafe { (p as *const u64).read_unaligned() };
    let mut scratch = vec![receiver];
    Ok(output_u64(vm, state, &mut scratch, value))
}

pub fn bytearray_read_i64(
    vm: &mut VM,
    state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let idx_v = args.get(0).copied().ok_or(RuntimeError::TypeError {
        expected: "index",
        got: Value::from_i64(0),
    })?;
    let index = expect_fixnum(idx_v)?;
    let p = bounds_checked_ptr(receiver, index, size_of::<i64>())?;
    let value = unsafe { (p as *const i64).read_unaligned() };
    let mut scratch = vec![receiver];
    Ok(output_i64(vm, state, &mut scratch, value))
}

pub fn bytearray_read_f32(
    vm: &mut VM,
    state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let idx_v = args.get(0).copied().ok_or(RuntimeError::TypeError {
        expected: "index",
        got: Value::from_i64(0),
    })?;
    let index = expect_fixnum(idx_v)?;
    let p = bounds_checked_ptr(receiver, index, size_of::<f32>())?;
    let value = unsafe { (p as *const f32).read_unaligned() } as f64;
    let mut scratch = vec![receiver];
    Ok(with_roots(vm, state, &mut scratch, |proxy, roots| unsafe {
        alloc_float(proxy, roots, value).value()
    }))
}

pub fn bytearray_read_f64(
    vm: &mut VM,
    state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let idx_v = args.get(0).copied().ok_or(RuntimeError::TypeError {
        expected: "index",
        got: Value::from_i64(0),
    })?;
    let index = expect_fixnum(idx_v)?;
    let p = bounds_checked_ptr(receiver, index, size_of::<f64>())?;
    let value = unsafe { (p as *const f64).read_unaligned() };
    let mut scratch = vec![receiver];
    Ok(with_roots(vm, state, &mut scratch, |proxy, roots| unsafe {
        alloc_float(proxy, roots, value).value()
    }))
}

pub fn bytearray_read_pointer(
    vm: &mut VM,
    state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let idx_v = args.get(0).copied().ok_or(RuntimeError::TypeError {
        expected: "index",
        got: Value::from_i64(0),
    })?;
    let index = expect_fixnum(idx_v)?;
    let p = bounds_checked_ptr(receiver, index, size_of::<u64>())?;
    let value = unsafe { (p as *const u64).read_unaligned() };
    let mut scratch = vec![receiver];
    Ok(with_roots(vm, state, &mut scratch, |proxy, roots| unsafe {
        alloc_alien(proxy, roots, value, 0).value()
    }))
}

macro_rules! bytearray_write_int {
    ($name:ident, $ty:ty) => {
        pub fn $name(
            _vm: &mut VM,
            _state: &mut InterpreterState,
            receiver: Value,
            args: &[Value],
        ) -> Result<Value, RuntimeError> {
            let idx_v =
                args.get(0).copied().ok_or(RuntimeError::TypeError {
                    expected: "index",
                    got: Value::from_i64(0),
                })?;
            let val_v =
                args.get(1).copied().ok_or(RuntimeError::TypeError {
                    expected: "value",
                    got: Value::from_i64(0),
                })?;
            let index = expect_fixnum(idx_v)?;
            let p = bounds_checked_ptr(receiver, index, size_of::<$ty>())?;
            let value = expect_fixnum(val_v)? as $ty;
            unsafe { (p as *mut $ty).write_unaligned(value) };
            Ok(receiver)
        }
    };
}

bytearray_write_int!(bytearray_write_u8, u8);
bytearray_write_int!(bytearray_write_i8, i8);
bytearray_write_int!(bytearray_write_u16, u16);
bytearray_write_int!(bytearray_write_i16, i16);
bytearray_write_int!(bytearray_write_u32, u32);
bytearray_write_int!(bytearray_write_i32, i32);

pub fn bytearray_write_u64(
    _vm: &mut VM,
    _state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let idx_v = args.get(0).copied().ok_or(RuntimeError::TypeError {
        expected: "index",
        got: Value::from_i64(0),
    })?;
    let val_v = args.get(1).copied().ok_or(RuntimeError::TypeError {
        expected: "value",
        got: Value::from_i64(0),
    })?;
    let index = expect_fixnum(idx_v)?;
    let p = bounds_checked_ptr(receiver, index, size_of::<u64>())?;
    let value = value_to_u64(val_v)?;
    unsafe { (p as *mut u64).write_unaligned(value) };
    Ok(receiver)
}

pub fn bytearray_write_i64(
    _vm: &mut VM,
    _state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let idx_v = args.get(0).copied().ok_or(RuntimeError::TypeError {
        expected: "index",
        got: Value::from_i64(0),
    })?;
    let val_v = args.get(1).copied().ok_or(RuntimeError::TypeError {
        expected: "value",
        got: Value::from_i64(0),
    })?;
    let index = expect_fixnum(idx_v)?;
    let p = bounds_checked_ptr(receiver, index, size_of::<i64>())?;
    let value = value_to_i64(val_v)?;
    unsafe { (p as *mut i64).write_unaligned(value) };
    Ok(receiver)
}

pub fn bytearray_write_f32(
    _vm: &mut VM,
    _state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let idx_v = args.get(0).copied().ok_or(RuntimeError::TypeError {
        expected: "index",
        got: Value::from_i64(0),
    })?;
    let val_v = args.get(1).copied().ok_or(RuntimeError::TypeError {
        expected: "float value",
        got: Value::from_i64(0),
    })?;
    let index = expect_fixnum(idx_v)?;
    let p = bounds_checked_ptr(receiver, index, size_of::<f32>())?;
    let value = if val_v.is_fixnum() {
        expect_fixnum(val_v)? as f32
    } else {
        unsafe { (*expect_float(val_v)?).value as f32 }
    };
    unsafe { (p as *mut f32).write_unaligned(value) };
    Ok(receiver)
}

pub fn bytearray_write_f64(
    _vm: &mut VM,
    _state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let idx_v = args.get(0).copied().ok_or(RuntimeError::TypeError {
        expected: "index",
        got: Value::from_i64(0),
    })?;
    let val_v = args.get(1).copied().ok_or(RuntimeError::TypeError {
        expected: "float value",
        got: Value::from_i64(0),
    })?;
    let index = expect_fixnum(idx_v)?;
    let p = bounds_checked_ptr(receiver, index, size_of::<f64>())?;
    let value = if val_v.is_fixnum() {
        expect_fixnum(val_v)? as f64
    } else {
        unsafe { (*expect_float(val_v)?).value }
    };
    unsafe { (p as *mut f64).write_unaligned(value) };
    Ok(receiver)
}

pub fn bytearray_write_pointer(
    _vm: &mut VM,
    _state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let idx_v = args.get(0).copied().ok_or(RuntimeError::TypeError {
        expected: "index",
        got: Value::from_i64(0),
    })?;
    let val_v = args.get(1).copied().ok_or(RuntimeError::TypeError {
        expected: "pointer value",
        got: Value::from_i64(0),
    })?;
    let index = expect_fixnum(idx_v)?;
    let p = bounds_checked_ptr(receiver, index, size_of::<u64>())?;
    let ptr_bits = if val_v.raw() == 0 {
        0
    } else if val_v.is_fixnum() {
        let n = expect_fixnum(val_v)?;
        if n < 0 {
            return Err(RuntimeError::Unimplemented {
                message: "pointer must be non-negative",
            });
        }
        n as u64
    } else {
        let a = expect_alien(val_v)?;
        unsafe { (*a).ptr }
    };
    unsafe { (p as *mut u64).write_unaligned(ptr_bits) };
    Ok(receiver)
}
