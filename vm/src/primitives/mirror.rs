use object::{Header, ObjectType, Slot, SlotObject, VMString, Value};

use crate::alloc::{add_constant_slot, remove_constant_slot};
use crate::interpreter::{with_roots, InterpreterState, RuntimeError};
use crate::primitives::{expect_fixnum, expect_string};
use crate::VM;

const REFLECTEE_SLOT: &str = "reflectee";

pub fn object_reflect(
    vm: &mut VM,
    state: &mut InterpreterState,
    _receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let reflectee = args.get(0).copied().ok_or(RuntimeError::TypeError {
        expected: "reflectee",
        got: Value::from_i64(0),
    })?;

    let mirror_proto = vm.special.mirror;
    let none = vm.special.none;

    let mirror = crate::primitives::object_clone::object_clone(
        vm,
        state,
        none,
        &[mirror_proto],
    )?;
    write_mirror_reflectee(vm, mirror, reflectee)?;
    Ok(mirror)
}

pub fn mirror_slot_count(
    _vm: &mut VM,
    _state: &mut InterpreterState,
    receiver: Value,
    _args: &[Value],
) -> Result<Value, RuntimeError> {
    let reflectee = mirror_reflectee(receiver)?;
    let map_val = reflectee_map(reflectee)?;
    let map: &object::Map = unsafe { map_val.as_ref() };
    let count = unsafe {
        map.slots()
            .iter()
            .filter(|slot| !slot.is_assignment())
            .count()
    };
    Ok(Value::from_i64(count as i64))
}

pub fn mirror_slot_name_at(
    _vm: &mut VM,
    _state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let idx_val = args.get(0).copied().ok_or(RuntimeError::TypeError {
        expected: "index",
        got: Value::from_i64(0),
    })?;
    let idx = expect_fixnum(idx_val)?;
    if idx < 0 {
        return Err(RuntimeError::Unimplemented {
            message: "mirror index must be non-negative",
        });
    }

    let reflectee = mirror_reflectee(receiver)?;
    let map_val = reflectee_map(reflectee)?;
    let map: &object::Map = unsafe { map_val.as_ref() };
    let mut n = 0_usize;
    for slot in unsafe { map.slots() } {
        if slot.is_assignment() {
            continue;
        }
        if n == idx as usize {
            return Ok(slot.name);
        }
        n += 1;
    }

    Err(RuntimeError::Unimplemented {
        message: "mirror index out of bounds",
    })
}

pub fn mirror_at(
    _vm: &mut VM,
    _state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let name = args.get(0).copied().ok_or(RuntimeError::TypeError {
        expected: "slot name",
        got: Value::from_i64(0),
    })?;
    let wanted = value_to_slot_name(name)?;

    let reflectee = mirror_reflectee(receiver)?;
    let reflectee_ptr = expect_slot_object_ptr(reflectee)?;
    let reflectee_obj: &SlotObject = unsafe { &*reflectee_ptr };
    let map_val = reflectee_map(reflectee)?;
    let map: &object::Map = unsafe { map_val.as_ref() };

    let slot = find_slot_by_name(map, &wanted).ok_or(
        RuntimeError::MessageNotUnderstood {
            receiver: reflectee,
            message: name,
        },
    )?;

    if slot.is_assignment() {
        return Err(RuntimeError::Unimplemented {
            message: "cannot read assignment slot",
        });
    }
    if slot.is_assignable() {
        let offset = unsafe { slot.value.to_i64() } as u32;
        return Ok(unsafe { reflectee_obj.read_value(offset) });
    }

    Ok(slot.value)
}

pub fn mirror_at_put(
    vm: &mut VM,
    _state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let name = args.get(0).copied().ok_or(RuntimeError::TypeError {
        expected: "slot name",
        got: Value::from_i64(0),
    })?;
    let value = args.get(1).copied().ok_or(RuntimeError::TypeError {
        expected: "slot value",
        got: Value::from_i64(0),
    })?;
    let wanted = value_to_slot_name(name)?;

    let reflectee = mirror_reflectee(receiver)?;
    let reflectee_ptr = expect_slot_object_ptr(reflectee)? as *mut SlotObject;
    let map_val = reflectee_map(reflectee)?;
    let map: &object::Map = unsafe { map_val.as_ref() };
    let slot = find_slot_by_name(map, &wanted).ok_or(
        RuntimeError::MessageNotUnderstood {
            receiver: reflectee,
            message: name,
        },
    )?;

    if slot.is_constant() {
        return Err(RuntimeError::Unimplemented {
            message: "slot is not assignable",
        });
    }
    if !slot.is_assignable() && !slot.is_assignment() {
        return Err(RuntimeError::Unimplemented {
            message: "slot is not writable",
        });
    }

    let offset = unsafe { slot.value.to_i64() } as u32;
    unsafe { (*reflectee_ptr).write_value(offset, value) };
    if value.is_ref() {
        vm.heap_proxy.write_barrier(reflectee, value);
    }
    Ok(value)
}

pub fn mirror_is_parent_at(
    vm: &mut VM,
    _state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let name = args.get(0).copied().ok_or(RuntimeError::TypeError {
        expected: "slot name",
        got: Value::from_i64(0),
    })?;
    let wanted = value_to_slot_name(name)?;

    let reflectee = mirror_reflectee(receiver)?;
    let map_val = reflectee_map(reflectee)?;
    let map: &object::Map = unsafe { map_val.as_ref() };
    let slot = find_slot_by_name(map, &wanted).ok_or(
        RuntimeError::MessageNotUnderstood {
            receiver: reflectee,
            message: name,
        },
    )?;

    Ok(if slot.is_parent() {
        vm.special.true_obj
    } else {
        vm.special.false_obj
    })
}

pub fn mirror_is_assignable_at(
    vm: &mut VM,
    _state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let name = args.get(0).copied().ok_or(RuntimeError::TypeError {
        expected: "slot name",
        got: Value::from_i64(0),
    })?;
    let wanted = value_to_slot_name(name)?;

    let reflectee = mirror_reflectee(receiver)?;
    let map_val = reflectee_map(reflectee)?;
    let map: &object::Map = unsafe { map_val.as_ref() };
    let slot = find_slot_by_name(map, &wanted).ok_or(
        RuntimeError::MessageNotUnderstood {
            receiver: reflectee,
            message: name,
        },
    )?;

    Ok(if slot.is_assignable() {
        vm.special.true_obj
    } else {
        vm.special.false_obj
    })
}

pub fn mirror_add_slot_value(
    vm: &mut VM,
    state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let name = args.get(0).copied().ok_or(RuntimeError::TypeError {
        expected: "slot name",
        got: Value::from_i64(0),
    })?;
    let value = args.get(1).copied().ok_or(RuntimeError::TypeError {
        expected: "slot value",
        got: Value::from_i64(0),
    })?;
    let name_ptr = expect_string(name)?;
    let wanted = unsafe { (*name_ptr).as_str() };

    let reflectee = mirror_reflectee(receiver)?;
    let reflectee_ptr = expect_slot_object_ptr(reflectee)? as *mut SlotObject;
    let old_map = unsafe { (*reflectee_ptr).map };
    let map_map = vm.special.map_map;
    let map_val = reflectee_map(reflectee)?;
    let map: &object::Map = unsafe { map_val.as_ref() };
    if find_slot_by_name(map, wanted).is_some() {
        return Err(RuntimeError::Unimplemented {
            message: "slot already exists",
        });
    }

    let name_symbol = intern_symbol(vm, state, name_ptr)?;
    let mut scratch = vec![reflectee, old_map, name_symbol, value];
    let new_map = with_roots(vm, state, &mut scratch, |proxy, roots| unsafe {
        add_constant_slot(proxy, roots, old_map, map_map, name_symbol, value)
    });

    unsafe { (*reflectee_ptr).map = new_map };
    vm.heap_proxy.write_barrier(reflectee, new_map);
    Ok(receiver)
}

pub fn mirror_remove_slot(
    vm: &mut VM,
    state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let name = args.get(0).copied().ok_or(RuntimeError::TypeError {
        expected: "slot name",
        got: Value::from_i64(0),
    })?;
    let wanted = value_to_slot_name(name)?;

    let reflectee = mirror_reflectee(receiver)?;
    let reflectee_ptr = expect_slot_object_ptr(reflectee)? as *mut SlotObject;
    let old_map = unsafe { (*reflectee_ptr).map };
    let map_map = vm.special.map_map;
    let map_val = reflectee_map(reflectee)?;
    let map: &object::Map = unsafe { map_val.as_ref() };
    let (slot, slot_index) = find_slot_by_name_with_index(map, &wanted).ok_or(
        RuntimeError::MessageNotUnderstood {
            receiver: reflectee,
            message: name,
        },
    )?;
    if !slot.is_constant() {
        return Err(RuntimeError::Unimplemented {
            message: "remove assignable slot unsupported",
        });
    }

    let mut scratch = vec![reflectee, old_map, name];
    let new_map = with_roots(vm, state, &mut scratch, |proxy, roots| unsafe {
        remove_constant_slot(proxy, roots, old_map, map_map, slot_index)
    });

    unsafe { (*reflectee_ptr).map = new_map };
    vm.heap_proxy.write_barrier(reflectee, new_map);
    Ok(receiver)
}

fn value_to_slot_name(name: Value) -> Result<String, RuntimeError> {
    let ptr = expect_string(name)?;
    Ok(unsafe { (*ptr).as_str() }.to_string())
}

fn mirror_reflectee(mirror: Value) -> Result<Value, RuntimeError> {
    let mirror_ptr = expect_slot_object_ptr(mirror)?;
    let mirror_obj: &SlotObject = unsafe { &*mirror_ptr };
    let mirror_map: &object::Map = unsafe { mirror_obj.map.as_ref() };
    let reflectee_slot = find_slot_by_name(mirror_map, REFLECTEE_SLOT).ok_or(
        RuntimeError::TypeError {
            expected: "mirror",
            got: mirror,
        },
    )?;

    if reflectee_slot.is_assignable() {
        let offset = unsafe { reflectee_slot.value.to_i64() } as u32;
        Ok(unsafe { mirror_obj.read_value(offset) })
    } else {
        Ok(reflectee_slot.value)
    }
}

fn write_mirror_reflectee(
    vm: &mut VM,
    mirror: Value,
    reflectee: Value,
) -> Result<(), RuntimeError> {
    let mirror_ptr = expect_slot_object_ptr(mirror)? as *mut SlotObject;
    let mirror_obj: &SlotObject = unsafe { &*mirror_ptr };
    let mirror_map: &object::Map = unsafe { mirror_obj.map.as_ref() };
    let reflectee_slot = find_slot_by_name(mirror_map, REFLECTEE_SLOT).ok_or(
        RuntimeError::TypeError {
            expected: "mirror",
            got: mirror,
        },
    )?;
    if !reflectee_slot.is_assignable() {
        return Err(RuntimeError::TypeError {
            expected: "assignable reflectee slot",
            got: mirror,
        });
    }

    let offset = unsafe { reflectee_slot.value.to_i64() } as u32;
    unsafe { (*mirror_ptr).write_value(offset, reflectee) };
    if reflectee.is_ref() {
        vm.heap_proxy.write_barrier(mirror, reflectee);
    }
    Ok(())
}

fn reflectee_map(reflectee: Value) -> Result<Value, RuntimeError> {
    let reflectee_ptr = expect_slot_object_ptr(reflectee)?;
    let reflectee_obj: &SlotObject = unsafe { &*reflectee_ptr };
    Ok(reflectee_obj.map)
}

fn find_slot_by_name(map: &object::Map, wanted: &str) -> Option<Slot> {
    unsafe {
        map.slots()
            .iter()
            .find(|slot| slot_name_eq(slot, wanted))
            .copied()
    }
}

fn find_slot_by_name_with_index(
    map: &object::Map,
    wanted: &str,
) -> Option<(Slot, u32)> {
    for (i, slot) in unsafe { map.slots() }.iter().enumerate() {
        if slot_name_eq(slot, wanted) {
            return Some((*slot, i as u32));
        }
    }
    None
}

fn slot_name_eq(slot: &Slot, wanted: &str) -> bool {
    if !slot.name.is_ref() {
        return false;
    }
    let header: &Header = unsafe { slot.name.as_ref() };
    if header.object_type() != ObjectType::Str {
        return false;
    }
    let name: &VMString = unsafe { slot.name.as_ref() };
    unsafe { name.as_str() == wanted }
}

fn intern_symbol(
    vm: &mut VM,
    state: &mut InterpreterState,
    name_ptr: *const VMString,
) -> Result<Value, RuntimeError> {
    let name = unsafe { (*name_ptr).as_str() };
    if let Some(&sym) = vm.intern_table.get(name) {
        return Ok(sym);
    }
    let sym =
        crate::primitives::string::alloc_vm_string(vm, state, name.as_bytes())?;
    vm.intern_table.insert(name.to_string(), sym);
    Ok(sym)
}

fn expect_slot_object_ptr(
    value: Value,
) -> Result<*const SlotObject, RuntimeError> {
    if !value.is_ref() {
        return Err(RuntimeError::TypeError {
            expected: "slot object",
            got: value,
        });
    }
    let header: &Header = unsafe { value.as_ref() };
    if header.object_type() != ObjectType::Slots {
        return Err(RuntimeError::TypeError {
            expected: "slot object",
            got: value,
        });
    }
    Ok(value.ref_bits() as *const SlotObject)
}
