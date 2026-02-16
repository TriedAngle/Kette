use object::Value;

use crate::interpreter::{
    primitive_extend_with, InterpreterState, RuntimeError,
};
use crate::VM;

pub fn extend_with(
    vm: &mut VM,
    state: &mut InterpreterState,
    _receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let target = args.get(0).copied().ok_or(RuntimeError::TypeError {
        expected: "target object",
        got: Value::from_i64(0),
    })?;
    let source = args.get(1).copied().ok_or(RuntimeError::TypeError {
        expected: "source object",
        got: Value::from_i64(0),
    })?;

    primitive_extend_with(vm, state, target, source)
}
