use object::Value;

use crate::interpreter::{with_roots, InterpreterState, RuntimeError};
use crate::VM;

pub fn object_become_with(
    vm: &mut VM,
    state: &mut InterpreterState,
    _receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let a = args.get(0).copied().ok_or(RuntimeError::TypeError {
        expected: "first object",
        got: Value::from_i64(0),
    })?;
    let b = args.get(1).copied().ok_or(RuntimeError::TypeError {
        expected: "second object",
        got: Value::from_i64(0),
    })?;

    if !a.is_ref() {
        return Err(RuntimeError::TypeError {
            expected: "heap object",
            got: a,
        });
    }
    if !b.is_ref() {
        return Err(RuntimeError::TypeError {
            expected: "heap object",
            got: b,
        });
    }
    if a.raw() == b.raw() {
        return Ok(a);
    }

    let mut scratch = vec![a, b];
    with_roots(vm, state, &mut scratch, |proxy, roots| {
        proxy.execute_become(a, b, roots);
    });

    Ok(a)
}
