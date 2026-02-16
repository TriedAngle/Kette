use object::Value;

use crate::interpreter::{call_block, InterpreterState, RuntimeError};
use crate::VM;

fn call_with_args(
    vm: &mut VM,
    state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    call_block(vm, state, receiver, args)
}

pub fn block_call0(
    vm: &mut VM,
    state: &mut InterpreterState,
    receiver: Value,
    _args: &[Value],
) -> Result<Value, RuntimeError> {
    call_with_args(vm, state, receiver, &[])
}

pub fn block_call1(
    vm: &mut VM,
    state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    call_with_args(vm, state, receiver, &args[..1])
}

pub fn block_call2(
    vm: &mut VM,
    state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    call_with_args(vm, state, receiver, &args[..2])
}

pub fn block_call3(
    vm: &mut VM,
    state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    call_with_args(vm, state, receiver, &args[..3])
}

pub fn block_call4(
    vm: &mut VM,
    state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    call_with_args(vm, state, receiver, &args[..4])
}

pub fn block_call5(
    vm: &mut VM,
    state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    call_with_args(vm, state, receiver, &args[..5])
}

pub fn block_call6(
    vm: &mut VM,
    state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    call_with_args(vm, state, receiver, &args[..6])
}

pub fn block_call7(
    vm: &mut VM,
    state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    call_with_args(vm, state, receiver, &args[..7])
}

pub fn block_call8(
    vm: &mut VM,
    state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    call_with_args(vm, state, receiver, &args[..8])
}
