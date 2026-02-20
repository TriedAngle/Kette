use object::{Array, BigNum, ByteArray, Header, ObjectType, SlotObject, Value};

use crate::alloc::{
    alloc_array, alloc_bignum_from_limbs, alloc_byte_array, alloc_float,
    alloc_ratio, alloc_slot_object,
};
use crate::interpreter::{with_roots, InterpreterState, RuntimeError};
use crate::primitives::{bool_value, string::alloc_vm_string};
use crate::VM;

pub fn object_eq(
    vm: &mut VM,
    _state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let rhs = args.get(0).copied().ok_or(RuntimeError::TypeError {
        expected: "rhs object",
        got: Value::from_i64(0),
    })?;
    Ok(bool_value(vm, receiver.raw() == rhs.raw()))
}

pub fn object_ne(
    vm: &mut VM,
    _state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let rhs = args.get(0).copied().ok_or(RuntimeError::TypeError {
        expected: "rhs object",
        got: Value::from_i64(0),
    })?;
    Ok(bool_value(vm, receiver.raw() != rhs.raw()))
}

pub fn object_clone(
    vm: &mut VM,
    state: &mut InterpreterState,
    _receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let target = args.get(0).copied().ok_or(RuntimeError::TypeError {
        expected: "object",
        got: Value::from_i64(0),
    })?;

    if target.is_fixnum() {
        return Ok(target);
    }

    if !target.is_ref() {
        return Err(RuntimeError::TypeError {
            expected: "object",
            got: target,
        });
    }

    let header: &Header = unsafe { target.as_ref() };
    let result = match header.object_type() {
        ObjectType::Slots => clone_slot_object(vm, state, target),
        ObjectType::Array => clone_array(vm, state, target),
        ObjectType::ByteArray => clone_bytearray(vm, state, target),
        ObjectType::Str => clone_string(vm, state, target),
        ObjectType::Symbol => Ok(target),
        ObjectType::Float => clone_float(vm, state, target),
        ObjectType::BigNum => clone_bignum(vm, state, target),
        ObjectType::Ratio => clone_ratio(vm, state, target),
        _ => Err(RuntimeError::Unimplemented {
            message: "clone not supported for object type",
        }),
    }?;

    #[cfg(debug_assertions)]
    {
        if let Some(name) = vm.trace_assoc_name.as_deref() {
            if let Some(global) = lookup_assoc_value(vm, name) {
                if global.raw() == target.raw() {
                    let target_info = value_summary(target);
                    let result_info = value_summary(result);
                    eprintln!(
                        "trace_clone {} target={} result={}",
                        name, target_info, result_info
                    );
                }
            }
        }
    }

    Ok(result)
}

#[cfg(debug_assertions)]
fn lookup_assoc_value(vm: &VM, name: &str) -> Option<Value> {
    let sym = vm.intern_table.get(name)?;
    unsafe {
        let dict: &SlotObject = vm.dictionary.as_ref();
        let map: &object::Map = dict.map.as_ref();
        for slot in map.slots() {
            if slot.name.raw() == sym.raw() {
                let assoc_obj: &SlotObject = slot.value.as_ref();
                return Some(assoc_obj.read_value(SlotObject::VALUES_OFFSET));
            }
        }
    }
    None
}

#[cfg(debug_assertions)]
fn value_summary(value: Value) -> String {
    if !value.is_ref() {
        if value.is_fixnum() {
            let n = unsafe { value.to_i64() };
            return format!("fixnum={n}");
        }
        return "immediate".to_string();
    }
    let header: &Header = unsafe { value.as_ref() };
    match header.object_type() {
        ObjectType::Slots => unsafe {
            let obj: &SlotObject = value.as_ref();
            let map: &object::Map = obj.map.as_ref();
            format!(
                "slots map_slots={} value_count={}",
                map.slot_count(),
                map.value_count()
            )
        },
        ObjectType::Map => unsafe {
            let map: &object::Map = value.as_ref();
            format!(
                "map slots={} value_count={}",
                map.slot_count(),
                map.value_count()
            )
        },
        _ => format!("{:?}", header.object_type()),
    }
}

fn clone_slot_object(
    vm: &mut VM,
    state: &mut InterpreterState,
    target: Value,
) -> Result<Value, RuntimeError> {
    let obj: &SlotObject = unsafe { target.as_ref() };
    let map_val = obj.map;
    let map: &object::Map = unsafe { map_val.as_ref() };
    let value_count = map.value_count() as usize;
    let mut values = Vec::with_capacity(value_count);
    for i in 0..value_count {
        let offset = SlotObject::VALUES_OFFSET + (i as u32 * 8);
        values.push(unsafe { obj.read_value(offset) });
    }

    let mut scratch = Vec::with_capacity(values.len() + 1);
    scratch.push(map_val);
    scratch.extend_from_slice(&values);
    let cloned = with_roots(vm, state, &mut scratch, |proxy, roots| unsafe {
        alloc_slot_object(proxy, roots, map_val, &values).value()
    });
    Ok(cloned)
}

fn clone_array(
    vm: &mut VM,
    state: &mut InterpreterState,
    target: Value,
) -> Result<Value, RuntimeError> {
    let arr: &Array = unsafe { target.as_ref() };
    let elements = unsafe { arr.elements() };
    let mut scratch = elements.to_vec();
    let cloned = with_roots(vm, state, &mut scratch, |proxy, roots| unsafe {
        alloc_array(proxy, roots, elements).value()
    });
    Ok(cloned)
}

fn clone_bytearray(
    vm: &mut VM,
    state: &mut InterpreterState,
    target: Value,
) -> Result<Value, RuntimeError> {
    let ba: &ByteArray = unsafe { target.as_ref() };
    let bytes = unsafe { ba.bytes() };
    let cloned =
        with_roots(vm, state, &mut Vec::new(), |proxy, roots| unsafe {
            alloc_byte_array(proxy, roots, bytes).value()
        });
    Ok(cloned)
}

fn clone_string(
    vm: &mut VM,
    state: &mut InterpreterState,
    target: Value,
) -> Result<Value, RuntimeError> {
    let str_ptr = crate::primitives::expect_string(target)?;
    let bytes = unsafe { (*str_ptr).as_bytes() };
    alloc_vm_string(vm, state, bytes)
}

fn clone_float(
    vm: &mut VM,
    state: &mut InterpreterState,
    target: Value,
) -> Result<Value, RuntimeError> {
    let f: &object::Float = unsafe { target.as_ref() };
    let value = f.value;
    let mut scratch = vec![target];
    let cloned = with_roots(vm, state, &mut scratch, |proxy, roots| unsafe {
        alloc_float(proxy, roots, value).value()
    });
    Ok(cloned)
}

fn clone_bignum(
    vm: &mut VM,
    state: &mut InterpreterState,
    target: Value,
) -> Result<Value, RuntimeError> {
    let b: &BigNum = unsafe { target.as_ref() };
    let sign = b.sign;
    let limbs = b.limbs();
    let mut scratch = vec![target];
    let cloned = with_roots(vm, state, &mut scratch, |proxy, roots| unsafe {
        alloc_bignum_from_limbs(proxy, roots, sign, limbs).value()
    });
    Ok(cloned)
}

fn clone_ratio(
    vm: &mut VM,
    state: &mut InterpreterState,
    target: Value,
) -> Result<Value, RuntimeError> {
    let ratio: &object::Ratio = unsafe { target.as_ref() };
    let numer = ratio.numerator;
    let denom = ratio.denominator;
    let mut scratch = vec![numer, denom];
    let cloned = with_roots(vm, state, &mut scratch, |proxy, roots| unsafe {
        alloc_ratio(proxy, roots, numer, denom).value()
    });
    Ok(cloned)
}
