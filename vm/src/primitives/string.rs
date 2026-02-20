use object::{init_symbol, Header, ObjectType, Value};

use crate::interpreter::{with_roots, InterpreterState, RuntimeError};
use crate::primitives::{bool_value, expect_string, expect_symbol};
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

pub fn string_to_symbol(
    vm: &mut VM,
    state: &mut InterpreterState,
    receiver: Value,
    _args: &[Value],
) -> Result<Value, RuntimeError> {
    let ptr = expect_string(receiver)?;
    let s = unsafe { (*ptr).as_str() };
    intern_symbol(vm, state, s)
}

pub fn symbol_to_string(
    vm: &mut VM,
    state: &mut InterpreterState,
    receiver: Value,
    _args: &[Value],
) -> Result<Value, RuntimeError> {
    let ptr = expect_symbol(receiver)?;
    let bytes = unsafe { (*ptr).as_bytes() };
    alloc_vm_string(vm, state, bytes)
}

pub fn symbol_length(
    _vm: &mut VM,
    _state: &mut InterpreterState,
    receiver: Value,
    _args: &[Value],
) -> Result<Value, RuntimeError> {
    let ptr = expect_symbol(receiver)?;
    let len = unsafe { (*ptr).len() } as i64;
    Ok(Value::from_i64(len))
}

pub fn symbol_eq(
    vm: &mut VM,
    _state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let rhs = args.get(0).copied().ok_or(RuntimeError::TypeError {
        expected: "symbol rhs",
        got: Value::from_i64(0),
    })?;

    if !rhs.is_ref() {
        return Ok(bool_value(vm, false));
    }

    let rhs_header: &Header = unsafe { rhs.as_ref() };
    if rhs_header.object_type() != ObjectType::Symbol {
        return Ok(bool_value(vm, false));
    }

    let _ = expect_symbol(receiver)?;
    let _ = expect_symbol(rhs)?;
    Ok(bool_value(vm, receiver.raw() == rhs.raw()))
}

pub fn symbol_ne(
    vm: &mut VM,
    state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let eq = symbol_eq(vm, state, receiver, args)?;
    Ok(bool_value(vm, eq.raw() == vm.special.false_obj.raw()))
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

pub(crate) fn alloc_vm_symbol(
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

        let size = std::mem::size_of::<object::VMSymbol>();
        let layout = std::alloc::Layout::from_size_align(size, 8).unwrap();
        let ptr = proxy.allocate(layout, roots);
        let sym_ptr = ptr.as_ptr() as *mut object::VMSymbol;
        init_symbol(sym_ptr, bytes.len() as u64, ba);
        Value::from_ptr(sym_ptr)
    });
    Ok(value)
}

pub(crate) fn intern_symbol(
    vm: &mut VM,
    state: &mut InterpreterState,
    name: &str,
) -> Result<Value, RuntimeError> {
    if let Some(&symbol) = vm.intern_table.get(name) {
        return Ok(symbol);
    }
    let symbol = alloc_vm_symbol(vm, state, name.as_bytes())?;
    let header: &Header = unsafe { symbol.as_ref() };
    debug_assert!(header.object_type() == ObjectType::Symbol);
    vm.intern_table.insert(name.to_string(), symbol);
    Ok(symbol)
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
