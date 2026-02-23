use object::{Array, Value};

use crate::alloc::alloc_array;
use crate::interpreter::{with_roots, InterpreterState, RuntimeError};
use crate::primitives::{expect_array, expect_fixnum};
use crate::VM;

pub fn array_size(
    _vm: &mut VM,
    _state: &mut InterpreterState,
    receiver: Value,
    _args: &[Value],
) -> Result<Value, RuntimeError> {
    let ptr = expect_array(receiver)?;
    Ok(Value::from_i64(unsafe { (*ptr).len() } as i64))
}

pub fn array_clone_with_size(
    vm: &mut VM,
    state: &mut InterpreterState,
    _receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let size_val = args.first().copied().ok_or(RuntimeError::TypeError {
        expected: "size",
        got: Value::from_i64(0),
    })?;
    let size = expect_fixnum(size_val)?;
    if size < 0 {
        return Err(RuntimeError::Unimplemented {
            message: "array size must be non-negative",
        });
    }

    let len = size as usize;
    let elements = vec![vm.special.none; len];
    let mut scratch = Vec::new();
    let arr = with_roots(vm, state, &mut scratch, |proxy, roots| unsafe {
        alloc_array(proxy, roots, &elements).value()
    });
    Ok(arr)
}

pub fn array_at(
    _vm: &mut VM,
    _state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let index_val = args.first().copied().ok_or(RuntimeError::TypeError {
        expected: "index",
        got: Value::from_i64(0),
    })?;
    let index = expect_fixnum(index_val)?;
    if index < 0 {
        return Err(RuntimeError::Unimplemented {
            message: "array index must be non-negative",
        });
    }

    let ptr = expect_array(receiver)?;
    let len = unsafe { (*ptr).len() } as i64;
    if index >= len {
        return Err(RuntimeError::Unimplemented {
            message: "array index out of bounds",
        });
    }

    let value = unsafe { (*ptr).element(index as u64) };
    Ok(value)
}

pub fn array_at_put(
    _vm: &mut VM,
    _state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let index_val = args.first().copied().ok_or(RuntimeError::TypeError {
        expected: "index",
        got: Value::from_i64(0),
    })?;
    let value = args.get(1).copied().ok_or(RuntimeError::TypeError {
        expected: "value",
        got: Value::from_i64(0),
    })?;

    let index = expect_fixnum(index_val)?;
    if index < 0 {
        return Err(RuntimeError::Unimplemented {
            message: "array index must be non-negative",
        });
    }

    let ptr = expect_array(receiver)? as *mut Array;
    let len = unsafe { (*ptr).len() } as i64;
    if index >= len {
        return Err(RuntimeError::Unimplemented {
            message: "array index out of bounds",
        });
    }

    unsafe {
        let elems = ptr.add(1) as *mut Value;
        *elems.add(index as usize) = value;
    }

    Ok(receiver)
}
