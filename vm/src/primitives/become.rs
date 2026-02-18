use std::collections::HashSet;
use std::sync::atomic::Ordering;

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

    let (_status, _generation, threads, _word) =
        vm.heap_proxy.heap.sync.state.load(Ordering::Acquire);
    if threads > 1 {
        return Err(RuntimeError::Unimplemented {
            message: "_Become:With: requires single mutator thread",
        });
    }

    let trace_fn = vm.heap_proxy.heap.trace_fn;
    let mut scratch = vec![a, b];
    with_roots(vm, state, &mut scratch, |proxy, roots| {
        become_full(proxy, roots, trace_fn, a, b);
    });

    Ok(a)
}

fn become_full(
    proxy: &mut heap::HeapProxy,
    roots: &mut dyn heap::RootProvider,
    trace_fn: heap::TraceFn,
    a: Value,
    b: Value,
) {
    let mut queue: Vec<*const u8> = Vec::new();
    let mut visited: HashSet<u64> = HashSet::new();

    roots.visit_roots(&mut |value| {
        swap_value(value, a, b);
        if value.is_ref() {
            queue.push(value.ref_bits() as *const u8);
        }
    });

    while let Some(obj_ptr) = queue.pop() {
        if !visited.insert(obj_ptr as u64) {
            continue;
        }
        let holder = Value::from_ptr(obj_ptr);
        unsafe {
            trace_fn(obj_ptr, &mut |field| {
                let changed = swap_value(field, a, b);
                if changed && field.is_ref() {
                    proxy.write_barrier(holder, *field);
                }
                if field.is_ref() {
                    queue.push(field.ref_bits() as *const u8);
                }
            });
        }
    }
}

fn swap_value(value: &mut Value, a: Value, b: Value) -> bool {
    if value.raw() == a.raw() {
        *value = b;
        true
    } else if value.raw() == b.raw() {
        *value = a;
        true
    } else {
        false
    }
}
