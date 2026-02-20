use object::{Map, ObjectType, SlotObject, Value};

use crate::interpreter::{InterpreterState, RuntimeError};
use crate::VM;

pub fn method_ensure_tail_call(
    _vm: &mut VM,
    _state: &mut InterpreterState,
    receiver: Value,
    _args: &[Value],
) -> Result<Value, RuntimeError> {
    if !receiver.is_ref() {
        return Err(RuntimeError::TypeError {
            expected: "method object",
            got: receiver,
        });
    }

    let header: &object::Header = unsafe { receiver.as_ref() };
    if header.object_type() != ObjectType::Slots {
        return Err(RuntimeError::TypeError {
            expected: "method object",
            got: receiver,
        });
    }

    let obj: &SlotObject = unsafe { receiver.as_ref() };
    let map: &Map = unsafe { obj.map.as_ref() };
    if !map.has_code() {
        return Err(RuntimeError::TypeError {
            expected: "method object",
            got: receiver,
        });
    }

    if !map.is_tail_call() {
        return Err(RuntimeError::Unimplemented {
            message: "method is not tail-call eligible",
        });
    }

    Ok(receiver)
}
