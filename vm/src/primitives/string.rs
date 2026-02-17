use object::Value;

use crate::interpreter::{with_roots, InterpreterState, RuntimeError};
use crate::primitives::expect_string;
use crate::VM;

pub fn string_print(
    _vm: &mut VM,
    _state: &mut InterpreterState,
    receiver: Value,
    _args: &[Value],
) -> Result<Value, RuntimeError> {
    let ptr = expect_string(receiver)?;
    let s = unsafe { (*ptr).as_str() };
    print!("{}", s);
    Ok(receiver)
}

pub fn string_println(
    _vm: &mut VM,
    _state: &mut InterpreterState,
    receiver: Value,
    _args: &[Value],
) -> Result<Value, RuntimeError> {
    let ptr = expect_string(receiver)?;
    let s = unsafe { (*ptr).as_str() };
    println!("{}", s);
    Ok(receiver)
}

pub fn string_length(
    _vm: &mut VM,
    _state: &mut InterpreterState,
    receiver: Value,
    _args: &[Value],
) -> Result<Value, RuntimeError> {
    let ptr = expect_string(receiver)?;
    let len = unsafe { (*ptr).len() } as i64;
    Ok(Value::from_i64(len))
}

pub fn string_to_bytearray(
    _vm: &mut VM,
    _state: &mut InterpreterState,
    receiver: Value,
    _args: &[Value],
) -> Result<Value, RuntimeError> {
    let ptr = expect_string(receiver)?;
    let data = unsafe { (*ptr).data };
    Ok(data)
}

pub(crate) fn alloc_vm_string(
    vm: &mut VM,
    state: &mut InterpreterState,
    bytes: &[u8],
) -> Result<Value, RuntimeError> {
    let mut scratch = Vec::new();
    let value = with_roots(vm, state, &mut scratch, |proxy, roots| unsafe {
        let mut data = Vec::with_capacity(bytes.len() + 1);
        data.extend_from_slice(bytes);
        data.push(0);
        let ba = crate::alloc::alloc_byte_array(proxy, roots, &data).value();
        roots.scratch.push(ba);

        let size = std::mem::size_of::<object::VMString>();
        let layout = std::alloc::Layout::from_size_align(size, 8).unwrap();
        let ptr = proxy.allocate(layout, roots);
        let str_ptr = ptr.as_ptr() as *mut object::VMString;
        object::init_str(str_ptr, bytes.len() as u64, ba);
        Value::from_ptr(str_ptr)
    });
    Ok(value)
}

pub(crate) fn alloc_vm_string_from_bytearray(
    vm: &mut VM,
    state: &mut InterpreterState,
    data: Value,
    length: u64,
) -> Result<Value, RuntimeError> {
    let mut scratch = vec![data];
    let value = with_roots(vm, state, &mut scratch, |proxy, roots| unsafe {
        let size = std::mem::size_of::<object::VMString>();
        let layout = std::alloc::Layout::from_size_align(size, 8).unwrap();
        let ptr = proxy.allocate(layout, roots);
        let str_ptr = ptr.as_ptr() as *mut object::VMString;
        object::init_str(str_ptr, length, data);
        Value::from_ptr(str_ptr)
    });
    Ok(value)
}
