use object::{Header, HeaderFlags, Value};

use crate::interpreter::{InterpreterState, RuntimeError};
use crate::VM;

fn expect_ref(value: Value) -> Result<*const Header, RuntimeError> {
    if !value.is_ref() {
        return Err(RuntimeError::TypeError {
            expected: "heap object",
            got: value,
        });
    }
    Ok(value.ref_bits() as *const Header)
}

pub fn object_pin(
    _vm: &mut VM,
    _state: &mut InterpreterState,
    _receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let value = args.get(0).copied().ok_or(RuntimeError::TypeError {
        expected: "value",
        got: Value::from_i64(0),
    })?;
    let header = expect_ref(value)?;
    unsafe { (*header).add_flag(HeaderFlags::PINNED) };
    Ok(value)
}

pub fn object_unpin(
    _vm: &mut VM,
    _state: &mut InterpreterState,
    _receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let value = args.get(0).copied().ok_or(RuntimeError::TypeError {
        expected: "value",
        got: Value::from_i64(0),
    })?;
    let header = expect_ref(value)?;
    unsafe { (*header).remove_flag(HeaderFlags::PINNED) };
    Ok(value)
}

pub fn object_is_pinned(
    vm: &mut VM,
    _state: &mut InterpreterState,
    _receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let value = args.get(0).copied().ok_or(RuntimeError::TypeError {
        expected: "value",
        got: Value::from_i64(0),
    })?;
    let header = expect_ref(value)?;
    let pinned = unsafe { (*header).has_flag(HeaderFlags::PINNED) };
    Ok(if pinned {
        vm.special.true_obj
    } else {
        vm.special.false_obj
    })
}
