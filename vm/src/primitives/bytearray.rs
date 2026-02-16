use object::Value;

use crate::interpreter::{InterpreterState, RuntimeError};
use crate::primitives::expect_bytearray;
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
