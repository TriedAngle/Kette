use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::sync::atomic::Ordering;

use bytecode::BytecodeBuilder;
use object::Value;
use object::{
    Array, Header, HeaderFlags, MapFlags, ObjectType, Slot, SlotFlags,
    SlotObject,
};
use parser::{Lexer, Parser};

use crate::compiler0;
use crate::interpreter::{
    self, call_block, install_finalizer, install_handler, request_unwind,
    signal_condition, with_roots, InterpreterState, RuntimeError,
};
use crate::materialize;
use crate::primitives::string::intern_symbol;
use crate::primitives::{
    expect_string, expect_symbol, string::alloc_vm_string,
};
use crate::threading;
use crate::{
    LockRecord, Monitor, PlatformThreadEntry, VMProxy, USER_MODULE, VM,
};

pub fn vm_eval(
    vm: &mut VM,
    state: &mut InterpreterState,
    _receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    if vm.current_module.is_none() {
        vm.open_module(USER_MODULE);
    }

    let source_ptr = expect_string(args[0])?;
    let source = unsafe { (*source_ptr).as_str() };

    let parse_results: Vec<_> = Parser::new(Lexer::from_str(source)).collect();
    let parse_errors: Vec<String> = parse_results
        .iter()
        .filter_map(|r| r.as_ref().err())
        .map(|e| format!("Parse error: {e}"))
        .collect();
    if !parse_errors.is_empty() {
        let msg = parse_errors.join("\n");
        return alloc_vm_string(vm, state, msg.as_bytes());
    }

    let exprs: Vec<parser::ast::Expr> =
        parse_results.into_iter().map(|r| r.unwrap()).collect();

    let code_desc = match compiler0::Compiler::compile_for_vm(vm, &exprs) {
        Ok(code_desc) => code_desc,
        Err(err) => {
            let msg = format!("Compile error: {err}");
            return alloc_vm_string(vm, state, msg.as_bytes());
        }
    };

    let code = materialize::materialize(vm, &code_desc);
    match interpreter::interpret(vm, code) {
        Ok(value) => Ok(value),
        Err(err) => {
            let msg = format_runtime_error(&err);
            alloc_vm_string(vm, state, msg.as_bytes())
        }
    }
}

fn format_runtime_error(err: &interpreter::LocatedRuntimeError) -> String {
    match err.location {
        Some(loc) => {
            format!(
                "Runtime error: {:?} at {}..{}",
                err.error, loc.start, loc.end
            )
        }
        None => format!("Runtime error: {:?}", err.error),
    }
}

pub fn vm_module_open(
    vm: &mut VM,
    _state: &mut InterpreterState,
    _receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let path = symbol_to_string(args[0])?;
    vm.open_module(&path);
    Ok(args[0])
}

pub fn vm_module_use(
    vm: &mut VM,
    _state: &mut InterpreterState,
    _receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let path = symbol_to_string(args[0])?;
    vm.module_use(&path, &HashMap::new()).map_err(|msg| {
        RuntimeError::Unimplemented {
            message: Box::leak(msg.into_boxed_str()),
        }
    })?;
    Ok(vm.special.none)
}

pub fn vm_module_use_as(
    vm: &mut VM,
    _state: &mut InterpreterState,
    _receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let path = symbol_to_string(args[0])?;
    let alias_map = parse_alias_map(args[1])?;
    vm.module_use(&path, &alias_map).map_err(|msg| {
        RuntimeError::Unimplemented {
            message: Box::leak(msg.into_boxed_str()),
        }
    })?;
    Ok(vm.special.none)
}

pub fn vm_module_use_only(
    vm: &mut VM,
    _state: &mut InterpreterState,
    _receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let path = symbol_to_string(args[0])?;
    let names = parse_symbol_names(args[1])?;
    vm.module_use_only(&path, &names).map_err(|msg| {
        RuntimeError::Unimplemented {
            message: Box::leak(msg.into_boxed_str()),
        }
    })?;
    Ok(vm.special.none)
}

pub fn vm_module_export(
    vm: &mut VM,
    _state: &mut InterpreterState,
    _receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let name = symbol_to_string(args[0])?;
    vm.module_export_current(&name).map_err(|msg| {
        RuntimeError::Unimplemented {
            message: Box::leak(msg.into_boxed_str()),
        }
    })?;
    Ok(vm.special.none)
}

pub fn vm_current_module(
    vm: &mut VM,
    state: &mut InterpreterState,
    _receiver: Value,
    _args: &[Value],
) -> Result<Value, RuntimeError> {
    let Some(path) = vm.current_module.clone() else {
        return Ok(vm.special.none);
    };
    intern_symbol(vm, state, &path)
}

pub fn vm_platform_os(
    vm: &mut VM,
    state: &mut InterpreterState,
    _receiver: Value,
    _args: &[Value],
) -> Result<Value, RuntimeError> {
    alloc_vm_string(vm, state, std::env::consts::OS.as_bytes())
}

pub fn vm_platform_arch(
    vm: &mut VM,
    state: &mut InterpreterState,
    _receiver: Value,
    _args: &[Value],
) -> Result<Value, RuntimeError> {
    alloc_vm_string(vm, state, std::env::consts::ARCH.as_bytes())
}

pub fn vm_with_handler_do(
    vm: &mut VM,
    state: &mut InterpreterState,
    _receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    install_handler(state, args[0]);
    call_block(vm, state, args[1], &[])?;
    Ok(vm.special.none)
}

pub fn vm_signal(
    vm: &mut VM,
    state: &mut InterpreterState,
    _receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    signal_condition(vm, state, args[0])?;
    Ok(vm.special.none)
}

pub fn vm_unwind(
    vm: &mut VM,
    state: &mut InterpreterState,
    _receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    request_unwind(state, args[0])?;
    Ok(vm.special.none)
}

pub fn vm_then_do(
    vm: &mut VM,
    state: &mut InterpreterState,
    _receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    install_finalizer(state, args[1]);
    call_block(vm, state, args[0], &[])?;
    Ok(vm.special.none)
}

pub fn vm_spawn_platform(
    vm: &mut VM,
    _state: &mut InterpreterState,
    _receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let mut builder = BytecodeBuilder::new();
    builder.load_constant(0);
    builder.send(1, 0, 0, 0);
    builder.local_return();

    let code_desc = compiler0::CodeDesc {
        bytecode: builder.into_bytes(),
        constants: vec![
            compiler0::ConstEntry::Value(args[0]),
            compiler0::ConstEntry::Symbol("call".to_string()),
        ],
        register_count: 1,
        arg_count: 0,
        temp_count: 0,
        feedback_count: 1,
        source_map: vec![],
    };

    let code = materialize::materialize(vm, &code_desc);
    let shared = vm.shared.clone();
    let id = vm.next_thread_id();

    let thread = crate::threading::spawn_platform(move || {
        let mut thread_vm = VMProxy::new(shared);
        match interpreter::interpret(&mut thread_vm, code) {
            Ok(value) => Ok(value),
            Err(err) => Err(format_runtime_error(&err)),
        }
    });

    vm.with_platform_threads(|threads| {
        threads.insert(
            id,
            PlatformThreadEntry {
                handle: thread,
                root_code: code,
            },
        );
    });
    Ok(Value::from_i64(id as i64))
}

pub fn vm_thread_join(
    vm: &mut VM,
    _state: &mut InterpreterState,
    _receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    if !args[0].is_fixnum() {
        return Err(RuntimeError::TypeError {
            expected: "thread handle id",
            got: args[0],
        });
    }
    let id = unsafe { args[0].to_i64() };
    if id <= 0 {
        return Err(RuntimeError::TypeError {
            expected: "thread handle id",
            got: args[0],
        });
    }
    let id = id as u64;

    let thread = vm
        .with_platform_threads(|threads| threads.remove(&id))
        .ok_or(RuntimeError::Unimplemented {
            message: "unknown platform thread handle",
        })?;

    match thread.handle.join() {
        Ok(Ok(value)) => Ok(value),
        Ok(Err(msg)) => Err(RuntimeError::Unimplemented {
            message: Box::leak(
                format!("platform thread failed: {msg}").into_boxed_str(),
            ),
        }),
        Err(_) => Err(RuntimeError::Unimplemented {
            message: "platform thread panicked",
        }),
    }
}

pub fn vm_thread_current(
    _vm: &mut VM,
    _state: &mut InterpreterState,
    _receiver: Value,
    _args: &[Value],
) -> Result<Value, RuntimeError> {
    let raw = threading::current_thread_token() & ((1u64 << 62) - 1);
    Ok(Value::from_i64(raw as i64))
}

pub fn vm_thread_yield(
    vm: &mut VM,
    _state: &mut InterpreterState,
    _receiver: Value,
    _args: &[Value],
) -> Result<Value, RuntimeError> {
    std::thread::yield_now();
    Ok(vm.special.none)
}

pub fn vm_thread_park(
    vm: &mut VM,
    _state: &mut InterpreterState,
    _receiver: Value,
    _args: &[Value],
) -> Result<Value, RuntimeError> {
    threading::park_current_thread();
    Ok(vm.special.none)
}

pub fn vm_thread_park_for_millis(
    vm: &mut VM,
    _state: &mut InterpreterState,
    _receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    if !args[0].is_fixnum() {
        return Err(RuntimeError::TypeError {
            expected: "millis",
            got: args[0],
        });
    }
    let millis = unsafe { args[0].to_i64() };
    if millis < 0 {
        return Err(RuntimeError::TypeError {
            expected: "non-negative millis",
            got: args[0],
        });
    }
    threading::park_current_thread_for(std::time::Duration::from_millis(
        millis as u64,
    ));
    Ok(vm.special.none)
}

pub fn vm_thread_unpark(
    vm: &mut VM,
    _state: &mut InterpreterState,
    _receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    if !args[0].is_fixnum() {
        return Err(RuntimeError::TypeError {
            expected: "thread token",
            got: args[0],
        });
    }
    let token = unsafe { args[0].to_i64() };
    if token <= 0 {
        return Err(RuntimeError::TypeError {
            expected: "thread token",
            got: args[0],
        });
    }
    if threading::unpark_thread(token as u64) {
        Ok(vm.special.true_obj)
    } else {
        Ok(vm.special.false_obj)
    }
}

pub fn vm_millis(
    _vm: &mut VM,
    _state: &mut InterpreterState,
    _receiver: Value,
    _args: &[Value],
) -> Result<Value, RuntimeError> {
    Ok(Value::from_i64(threading::monotonic_millis() as i64))
}

pub fn vm_unix_time(
    _vm: &mut VM,
    _state: &mut InterpreterState,
    _receiver: Value,
    _args: &[Value],
) -> Result<Value, RuntimeError> {
    Ok(Value::from_i64(threading::unix_time_seconds()))
}

const LOCK_STATE_MASK: u8 = HeaderFlags::LOCK_MASK.0;
const LOCK_STATE_UNLOCKED: u8 = HeaderFlags::LOCK_UNLOCKED.0;
const LOCK_STATE_THIN: u8 = HeaderFlags::LOCK_THIN.0;
const LOCK_STATE_INFLATING: u8 = HeaderFlags::LOCK_INFLATING.0;
const LOCK_STATE_INFLATED: u8 = HeaderFlags::LOCK_INFLATED.0;

thread_local! {
    static THIN_LOCKS: RefCell<HashMap<u64, u32>> = RefCell::new(HashMap::new());
}

#[inline(always)]
fn lock_state(flags: u8) -> u8 {
    flags & LOCK_STATE_MASK
}

#[inline(always)]
fn with_lock_state(flags: u8, state: u8) -> u8 {
    (flags & !LOCK_STATE_MASK) | state
}

#[inline(always)]
fn thin_depth(key: u64) -> Option<u32> {
    THIN_LOCKS.with(|locks| locks.borrow().get(&key).copied())
}

#[inline(always)]
fn thin_set_depth(key: u64, depth: u32) {
    THIN_LOCKS.with(|locks| {
        locks.borrow_mut().insert(key, depth);
    });
}

#[inline(always)]
fn thin_remove(key: u64) {
    THIN_LOCKS.with(|locks| {
        locks.borrow_mut().remove(&key);
    });
}

fn ensure_ref_object(
    value: Value,
    what: &'static str,
) -> Result<(), RuntimeError> {
    if !value.is_ref() {
        return Err(RuntimeError::TypeError {
            expected: what,
            got: value,
        });
    }
    Ok(())
}

fn pin_monitor_target(value: Value) {
    if !value.is_ref() {
        return;
    }
    let header: &Header = unsafe { value.as_ref() };
    header.add_flag(HeaderFlags::PINNED);
}

fn lock_record_for(vm: &mut VM, target: Value) -> std::sync::Arc<LockRecord> {
    let key = target.ref_bits();
    let mut table = vm.lock_records.lock().expect("lock table poisoned");
    table
        .entry(key)
        .or_insert_with(|| {
            std::sync::Arc::new(LockRecord {
                monitor: std::sync::Mutex::new(None),
            })
        })
        .clone()
}

fn monitor_for_record(
    record: &std::sync::Arc<LockRecord>,
) -> std::sync::Arc<Monitor> {
    let mut monitor = record.monitor.lock().expect("monitor slot poisoned");
    monitor
        .get_or_insert_with(|| {
            std::sync::Arc::new(Monitor {
                state: std::sync::Mutex::new(Default::default()),
                cvar: std::sync::Condvar::new(),
            })
        })
        .clone()
}

fn monitor_enter_slow(monitor: &Monitor, token: u64) {
    let mut guard = monitor.state.lock().expect("monitor state poisoned");
    loop {
        match guard.owner {
            None => {
                guard.owner = Some(token);
                guard.recursion = 1;
                return;
            }
            Some(owner) if owner == token => {
                guard.recursion = guard.recursion.saturating_add(1);
                return;
            }
            _ => {
                guard =
                    monitor.cvar.wait(guard).expect("monitor wait poisoned");
            }
        }
    }
}

fn monitor_exit_slow(
    monitor: &Monitor,
    token: u64,
) -> Result<(), RuntimeError> {
    let mut guard = monitor.state.lock().expect("monitor state poisoned");
    if guard.owner != Some(token) {
        return Err(RuntimeError::Unimplemented {
            message: "monitor exit without ownership",
        });
    }
    if guard.recursion > 1 {
        guard.recursion -= 1;
    } else {
        guard.owner = None;
        guard.recursion = 0;
        monitor.cvar.notify_one();
    }
    Ok(())
}

fn inflate_after_contention(
    vm: &mut VM,
    target: Value,
    header: &Header,
    token: u64,
) {
    let record = lock_record_for(vm, target);
    let monitor = monitor_for_record(&record);
    loop {
        let flags = header.flags_acquire().0;
        match lock_state(flags) {
            LOCK_STATE_UNLOCKED => {
                let next = with_lock_state(flags, LOCK_STATE_INFLATED);
                if header
                    .compare_exchange_flags(
                        HeaderFlags(flags),
                        HeaderFlags(next),
                        Ordering::AcqRel,
                        Ordering::Acquire,
                    )
                    .is_ok()
                {
                    monitor_enter_slow(&monitor, token);
                    return;
                }
            }
            LOCK_STATE_THIN => {
                let next = with_lock_state(flags, LOCK_STATE_INFLATING);
                if header
                    .compare_exchange_flags(
                        HeaderFlags(flags),
                        HeaderFlags(next),
                        Ordering::AcqRel,
                        Ordering::Acquire,
                    )
                    .is_ok()
                {
                    continue;
                }
            }
            LOCK_STATE_INFLATING => {
                std::thread::yield_now();
            }
            LOCK_STATE_INFLATED => {
                monitor_enter_slow(&monitor, token);
                return;
            }
            _ => unreachable!("invalid lock state"),
        }
    }
}

fn ensure_inflated_owned(
    vm: &mut VM,
    target: Value,
    header: &Header,
    token: u64,
) -> Result<std::sync::Arc<Monitor>, RuntimeError> {
    let key = target.ref_bits();
    if let Some(depth) = thin_depth(key) {
        let record = lock_record_for(vm, target);
        let monitor = monitor_for_record(&record);
        {
            let mut guard =
                monitor.state.lock().expect("monitor state poisoned");
            guard.owner = Some(token);
            guard.recursion = depth.max(1);
        }
        loop {
            let flags = header.flags_acquire().0;
            if lock_state(flags) == LOCK_STATE_INFLATED {
                break;
            }
            if lock_state(flags) != LOCK_STATE_THIN {
                return Err(RuntimeError::Unimplemented {
                    message: "invalid lock state during inflation",
                });
            }
            let next = with_lock_state(flags, LOCK_STATE_INFLATED);
            if header
                .compare_exchange_flags(
                    HeaderFlags(flags),
                    HeaderFlags(next),
                    Ordering::AcqRel,
                    Ordering::Acquire,
                )
                .is_ok()
            {
                break;
            }
        }
        thin_remove(key);
        return Ok(monitor);
    }

    let record = lock_record_for(vm, target);
    Ok(monitor_for_record(&record))
}

pub fn vm_monitor_enter(
    vm: &mut VM,
    _state: &mut InterpreterState,
    _receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let target = args[0];
    ensure_ref_object(target, "monitor target")?;
    pin_monitor_target(target);
    let header: &Header = unsafe { target.as_ref() };
    let key = target.ref_bits();
    let token = threading::current_thread_token();

    if let Some(depth) = thin_depth(key) {
        thin_set_depth(key, depth.saturating_add(1));
        return Ok(vm.special.none);
    }

    loop {
        let flags = header.flags_acquire().0;
        match lock_state(flags) {
            LOCK_STATE_UNLOCKED => {
                let next = with_lock_state(flags, LOCK_STATE_THIN);
                if header
                    .compare_exchange_flags(
                        HeaderFlags(flags),
                        HeaderFlags(next),
                        Ordering::AcqRel,
                        Ordering::Acquire,
                    )
                    .is_ok()
                {
                    thin_set_depth(key, 1);
                    return Ok(vm.special.none);
                }
            }
            LOCK_STATE_THIN => {
                inflate_after_contention(vm, target, header, token);
                return Ok(vm.special.none);
            }
            LOCK_STATE_INFLATING => std::thread::yield_now(),
            LOCK_STATE_INFLATED => {
                let record = lock_record_for(vm, target);
                let monitor = monitor_for_record(&record);
                monitor_enter_slow(&monitor, token);
                return Ok(vm.special.none);
            }
            _ => unreachable!("invalid lock state"),
        }
    }
}

pub fn vm_monitor_exit(
    vm: &mut VM,
    _state: &mut InterpreterState,
    _receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let target = args[0];
    ensure_ref_object(target, "monitor target")?;
    let header: &Header = unsafe { target.as_ref() };
    let key = target.ref_bits();
    let token = threading::current_thread_token();

    if let Some(depth) = thin_depth(key) {
        if depth > 1 {
            thin_set_depth(key, depth - 1);
            return Ok(vm.special.none);
        }
        thin_remove(key);
        loop {
            let flags = header.flags_acquire().0;
            match lock_state(flags) {
                LOCK_STATE_THIN => {
                    let next = with_lock_state(flags, LOCK_STATE_UNLOCKED);
                    if header
                        .compare_exchange_flags(
                            HeaderFlags(flags),
                            HeaderFlags(next),
                            Ordering::AcqRel,
                            Ordering::Acquire,
                        )
                        .is_ok()
                    {
                        return Ok(vm.special.none);
                    }
                }
                LOCK_STATE_INFLATING => {
                    let record = lock_record_for(vm, target);
                    let monitor = monitor_for_record(&record);
                    {
                        let mut guard = monitor
                            .state
                            .lock()
                            .expect("monitor state poisoned");
                        guard.owner = Some(token);
                        guard.recursion = 1;
                    }
                    let next = with_lock_state(flags, LOCK_STATE_INFLATED);
                    if header
                        .compare_exchange_flags(
                            HeaderFlags(flags),
                            HeaderFlags(next),
                            Ordering::AcqRel,
                            Ordering::Acquire,
                        )
                        .is_ok()
                    {
                        monitor_exit_slow(&monitor, token)?;
                        return Ok(vm.special.none);
                    }
                }
                LOCK_STATE_INFLATED => {
                    let record = lock_record_for(vm, target);
                    let monitor = monitor_for_record(&record);
                    monitor_exit_slow(&monitor, token)?;
                    return Ok(vm.special.none);
                }
                _ => {
                    return Err(RuntimeError::Unimplemented {
                        message: "monitor exit without ownership",
                    });
                }
            }
        }
    }

    if lock_state(header.flags_acquire().0) == LOCK_STATE_INFLATED {
        let record = lock_record_for(vm, target);
        let monitor = monitor_for_record(&record);
        monitor_exit_slow(&monitor, token)?;
        return Ok(vm.special.none);
    }

    Err(RuntimeError::Unimplemented {
        message: "monitor exit without ownership",
    })
}

pub fn vm_monitor_wait(
    vm: &mut VM,
    _state: &mut InterpreterState,
    _receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let target = args[0];
    ensure_ref_object(target, "monitor target")?;
    let header: &Header = unsafe { target.as_ref() };
    let token = threading::current_thread_token();

    let monitor = ensure_inflated_owned(vm, target, header, token)?;

    let mut guard = monitor.state.lock().expect("monitor state poisoned");
    if guard.owner != Some(token) {
        return Err(RuntimeError::Unimplemented {
            message: "monitor wait without ownership",
        });
    }
    let depth = guard.recursion.max(1);
    guard.owner = None;
    guard.recursion = 0;
    monitor.cvar.notify_one();
    loop {
        guard = monitor.cvar.wait(guard).expect("monitor wait poisoned");
        if guard.owner.is_none() {
            guard.owner = Some(token);
            guard.recursion = depth;
            return Ok(vm.special.none);
        }
    }
}

pub fn vm_monitor_notify(
    vm: &mut VM,
    _state: &mut InterpreterState,
    _receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let target = args[0];
    ensure_ref_object(target, "monitor target")?;
    let header: &Header = unsafe { target.as_ref() };
    let token = threading::current_thread_token();

    if thin_depth(target.ref_bits()).is_some() {
        return Ok(vm.special.none);
    }

    if lock_state(header.flags_acquire().0) != LOCK_STATE_INFLATED {
        return Err(RuntimeError::Unimplemented {
            message: "monitor notify without ownership",
        });
    }

    let record = lock_record_for(vm, target);
    let monitor = monitor_for_record(&record);
    let guard = monitor.state.lock().expect("monitor state poisoned");
    if guard.owner != Some(token) {
        return Err(RuntimeError::Unimplemented {
            message: "monitor notify without ownership",
        });
    }
    drop(guard);
    monitor.cvar.notify_one();
    Ok(vm.special.none)
}

pub fn vm_monitor_notify_all(
    vm: &mut VM,
    _state: &mut InterpreterState,
    _receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let target = args[0];
    ensure_ref_object(target, "monitor target")?;
    let header: &Header = unsafe { target.as_ref() };
    let token = threading::current_thread_token();

    if thin_depth(target.ref_bits()).is_some() {
        return Ok(vm.special.none);
    }

    if lock_state(header.flags_acquire().0) != LOCK_STATE_INFLATED {
        return Err(RuntimeError::Unimplemented {
            message: "monitor notifyAll without ownership",
        });
    }

    let record = lock_record_for(vm, target);
    let monitor = monitor_for_record(&record);
    let guard = monitor.state.lock().expect("monitor state poisoned");
    if guard.owner != Some(token) {
        return Err(RuntimeError::Unimplemented {
            message: "monitor notifyAll without ownership",
        });
    }
    drop(guard);
    monitor.cvar.notify_all();
    Ok(vm.special.none)
}

pub fn vm_module_at(
    vm: &mut VM,
    state: &mut InterpreterState,
    _receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let path = symbol_to_string(args[0])?;
    let entries = vm.module_public_entries(&path).map_err(|msg| {
        RuntimeError::Unimplemented {
            message: Box::leak(msg.into_boxed_str()),
        }
    })?;

    let mut slot_data = Vec::with_capacity(entries.len());
    let mut scratch = Vec::with_capacity(entries.len() * 2);
    for (name, value) in &entries {
        let sym = intern_symbol(vm, state, name)?;
        slot_data.push((sym, *value));
        scratch.push(sym);
        scratch.push(*value);
    }

    let obj = with_roots(vm, state, &mut scratch, |proxy, roots| unsafe {
        let map_map = roots.special.map_map;
        let none = roots.special.none;
        let mut slots = Vec::with_capacity(slot_data.len());
        for (sym, value) in &slot_data {
            slots.push(Slot::new(
                SlotFlags::CONSTANT.with(SlotFlags::ENUMERABLE),
                *sym,
                *value,
            ));
        }

        let map = crate::alloc::alloc_map(
            proxy,
            roots,
            map_map,
            none,
            MapFlags::NONE,
            &slots,
            0,
        )
        .value();
        crate::alloc::alloc_slot_object(proxy, roots, map, &[]).value()
    });
    Ok(obj)
}

fn symbol_to_string(value: Value) -> Result<String, RuntimeError> {
    let ptr = expect_symbol(value)?;
    let s: &object::VMSymbol = unsafe { &*ptr };
    Ok(unsafe { s.as_str() }.to_string())
}

fn parse_alias_map(
    value: Value,
) -> Result<HashMap<String, String>, RuntimeError> {
    if !value.is_ref() {
        return Err(RuntimeError::TypeError {
            expected: "alias object",
            got: value,
        });
    }
    let header: &object::Header = unsafe { value.as_ref() };
    if header.object_type() != ObjectType::Slots {
        return Err(RuntimeError::TypeError {
            expected: "alias object",
            got: value,
        });
    }

    let obj: &SlotObject = unsafe { value.as_ref() };
    let map: &object::Map = unsafe { obj.map.as_ref() };
    let mut aliases = HashMap::new();
    unsafe {
        for slot in map.slots() {
            let from_name = symbol_to_string(slot.name)?;
            let to_value = if slot.is_assignable() {
                let offset = slot.value.to_i64() as u32;
                obj.read_value(offset)
            } else {
                slot.value
            };
            let to_name = symbol_to_string(to_value)?;
            aliases.insert(from_name, to_name);
        }
    }
    Ok(aliases)
}

fn parse_symbol_names(value: Value) -> Result<HashSet<String>, RuntimeError> {
    let mut names = HashSet::new();

    if value.is_ref() {
        let header: &object::Header = unsafe { value.as_ref() };
        if header.object_type() == ObjectType::Array {
            let array: &Array = unsafe { value.as_ref() };
            for element in unsafe { array.elements() } {
                names.insert(symbol_to_string(*element)?);
            }
            return Ok(names);
        }
    }

    names.insert(symbol_to_string(value)?);
    Ok(names)
}

#[cfg(test)]
mod tests {
    use super::*;
    use heap::HeapSettings;
    use object::{Header, ObjectType, VMString, Value};
    use std::fs;
    use std::time::Instant;

    fn execute_source(vm: &mut VM, source: &str) -> Result<Value, String> {
        if vm.current_module.is_none() {
            vm.open_module(USER_MODULE);
        }

        let parse_results: Vec<_> =
            Parser::new(Lexer::from_str(source)).collect();
        let parse_errors: Vec<String> = parse_results
            .iter()
            .filter_map(|r| r.as_ref().err())
            .map(|e| format!("Parse error: {e}"))
            .collect();
        if !parse_errors.is_empty() {
            return Err(parse_errors.join("\n"));
        }

        let exprs: Vec<parser::ast::Expr> =
            parse_results.into_iter().map(|r| r.unwrap()).collect();
        let code_desc = compiler0::Compiler::compile_for_vm(vm, &exprs)
            .map_err(|e| format!("Compile error: {e}"))?;
        let code = materialize::materialize(vm, &code_desc);
        interpreter::interpret(vm, code)
            .map(|v| v)
            .map_err(|e| format!("Runtime error: {:?}", e.error))
    }

    fn as_string(value: Value) -> Option<String> {
        if !value.is_ref() {
            return None;
        }
        let header: &Header = unsafe { value.as_ref() };
        if header.object_type() != ObjectType::Str {
            return None;
        }
        let s: &VMString = unsafe { value.as_ref() };
        Some(unsafe { s.as_str() }.to_string())
    }

    fn compile_source(
        vm: &mut VM,
        source: &str,
    ) -> Result<compiler0::CodeDesc, String> {
        if vm.current_module.is_none() {
            vm.open_module(USER_MODULE);
        }

        let parse_results: Vec<_> =
            Parser::new(Lexer::from_str(source)).collect();
        let parse_errors: Vec<String> = parse_results
            .iter()
            .filter_map(|r| r.as_ref().err())
            .map(|e| format!("Parse error: {e}"))
            .collect();
        if !parse_errors.is_empty() {
            return Err(parse_errors.join("\n"));
        }

        let exprs: Vec<parser::ast::Expr> =
            parse_results.into_iter().map(|r| r.unwrap()).collect();
        compiler0::Compiler::compile_for_vm(vm, &exprs)
            .map_err(|e| format!("Compile error: {e}"))
    }

    fn load_core_init(vm: &mut VM) {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../core/init.ktt");
        let source =
            fs::read_to_string(path).expect("read core/init.ktt for test");
        execute_source(vm, &source).expect("load core/init.ktt");
    }

    fn load_core_math(vm: &mut VM) {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../core/math.ktt");
        let source =
            fs::read_to_string(path).expect("read core/math.ktt for test");
        execute_source(vm, &source).expect("load core/math.ktt");
    }

    fn load_core_collections(vm: &mut VM) {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../core/collections.ktt");
        let source = fs::read_to_string(path)
            .expect("read core/collections.ktt for test");
        execute_source(vm, &source).expect("load core/collections.ktt");
    }

    #[test]
    fn eval_computes_value_in_global_scope() {
        let mut vm = crate::special::bootstrap(HeapSettings::default());
        let value = execute_source(&mut vm, "VM _Eval: \"40 _FixnumAdd: 2\"")
            .expect("evaluation should succeed");
        assert!(value.is_fixnum());
        assert_eq!(unsafe { value.to_i64() }, 42);
    }

    #[test]
    fn eval_updates_globals() {
        let mut vm = crate::special::bootstrap(HeapSettings::default());
        let value = execute_source(
            &mut vm,
            "EvalGlobal := 0. VM _Eval: \"EvalGlobal := 41.\". EvalGlobal _FixnumAdd: 1",
        )
        .expect("evaluation should succeed");
        assert!(value.is_fixnum());
        assert_eq!(unsafe { value.to_i64() }, 42);
    }

    #[test]
    fn eval_does_not_capture_caller_locals() {
        let mut vm = crate::special::bootstrap(HeapSettings::default());
        let value = execute_source(
            &mut vm,
            "{ test = { local := 99. VM _Eval: \"local\" }. } test",
        )
        .expect("evaluation should succeed");
        let text =
            as_string(value).expect("eval should return an error string");
        assert!(text.contains("Compile error"));
        assert!(text.contains("local"));
    }

    #[test]
    fn eval_returns_parse_errors_as_string() {
        let mut vm = crate::special::bootstrap(HeapSettings::default());
        let value = execute_source(&mut vm, "VM _Eval: \"(\"")
            .expect("eval call should succeed");
        let text =
            as_string(value).expect("eval should return an error string");
        assert!(text.contains("Parse error"));
    }

    #[test]
    fn vm_proxy_allows_parallel_eval() {
        let vm = crate::special::bootstrap(HeapSettings::default());
        let shared = vm.shared.clone();

        let handle_left = std::thread::spawn({
            let shared = shared.clone();
            move || {
                let mut proxy = crate::VMProxy::new(shared);
                execute_source(&mut proxy, "1 _FixnumAdd: 2")
            }
        });

        let handle_right = std::thread::spawn({
            let shared = shared.clone();
            move || {
                let mut proxy = crate::VMProxy::new(shared);
                execute_source(&mut proxy, "40 _FixnumAdd: 2")
            }
        });

        let left = handle_left.join().expect("join left thread");
        let right = handle_right.join().expect("join right thread");

        let left_value = left.expect("left evaluation");
        let right_value = right.expect("right evaluation");
        assert!(left_value.is_fixnum());
        assert!(right_value.is_fixnum());
        assert_eq!(unsafe { left_value.to_i64() }, 3);
        assert_eq!(unsafe { right_value.to_i64() }, 42);
    }

    #[test]
    fn modules_isolate_bindings_without_global_fallback() {
        let mut vm = crate::special::bootstrap(HeapSettings::default());
        let err = execute_source(
            &mut vm,
            "VM _ModuleOpen: 'Shared. GlobalX := 9. VM _ModuleExport: 'GlobalX. VM _ModuleOpen: 'A. x := 1. VM _ModuleOpen: 'B. x := 2. VM _ModuleOpen: 'A. x _FixnumAdd: GlobalX",
        )
        .expect_err("cross-module global without import should fail");
        assert!(err.contains("unresolved global 'GlobalX'"));

        let value = execute_source(
            &mut vm,
            "VM _ModuleOpen: 'Shared. GlobalX := 9. VM _ModuleExport: 'GlobalX. VM _ModuleOpen: 'A. x := 1. VM _ModuleUse: 'Shared. x _FixnumAdd: GlobalX",
        )
        .expect("explicit module import should succeed");
        assert!(value.is_fixnum());
        assert_eq!(unsafe { value.to_i64() }, 10);
    }

    #[test]
    fn module_use_imports_only_exports() {
        let mut vm = crate::special::bootstrap(HeapSettings::default());
        let value = execute_source(
            &mut vm,
            "VM _ModuleOpen: 'Lib. foo := 41. hidden := 7. VM _ModuleExport: 'foo. VM _ModuleOpen: 'App. VM _ModuleUse: 'Lib. foo _FixnumAdd: 1",
        )
        .expect("module use should import exported names");
        assert!(value.is_fixnum());
        assert_eq!(unsafe { value.to_i64() }, 42);

        let err = execute_source(&mut vm, "VM _ModuleOpen: 'App. hidden")
            .expect_err("hidden must not be imported");
        assert!(err.contains("unresolved global 'hidden'"));
    }

    #[test]
    fn module_use_only_imports_requested_name() {
        let mut vm = crate::special::bootstrap(HeapSettings::default());
        let value = execute_source(
            &mut vm,
            "VM _ModuleOpen: 'Lib. foo := 41. bar := 7. VM _ModuleExport: 'foo. VM _ModuleExport: 'bar. VM _ModuleOpen: 'App. VM _ModuleUseOnly: 'Lib Names: 'foo. foo _FixnumAdd: 1",
        )
        .expect("use only should import requested name");
        assert!(value.is_fixnum());
        assert_eq!(unsafe { value.to_i64() }, 42);

        let err = execute_source(&mut vm, "VM _ModuleOpen: 'App. bar")
            .expect_err("non-selected export must not be imported");
        assert!(err.contains("unresolved global 'bar'"));
    }

    #[test]
    fn module_use_as_aliases_and_collisions_are_atomic() {
        let mut vm = crate::special::bootstrap(HeapSettings::default());
        execute_source(
            &mut vm,
            "VM _ModuleOpen: 'A. foo := 1. VM _ModuleExport: 'foo.",
        )
        .expect("setup A");
        execute_source(
            &mut vm,
            "VM _ModuleOpen: 'B. foo := 2. VM _ModuleExport: 'foo.",
        )
        .expect("setup B");

        execute_source(
            &mut vm,
            "VM _ModuleOpen: 'App. VM _ModuleUse: 'A As: { foo = 'fromA }. fromA",
        )
        .expect("first import should succeed");

        let err = execute_source(
            &mut vm,
            "VM _ModuleOpen: 'App. VM _ModuleUse: 'B As: { foo = 'fromA }",
        )
        .expect_err("alias collision should fail");
        assert!(err.contains("import collision"));

        let value = execute_source(&mut vm, "VM _ModuleOpen: 'App. fromA")
            .expect("existing import must remain unchanged");
        assert!(value.is_fixnum());
        assert_eq!(unsafe { value.to_i64() }, 1);
    }

    #[test]
    fn module_at_exposes_public_surface_only() {
        let mut vm = crate::special::bootstrap(HeapSettings::default());
        execute_source(
            &mut vm,
            "VM _ModuleOpen: 'Lib. pub := 3. hidden := 7. VM _ModuleExport: 'pub.",
        )
        .expect("setup lib module");

        let value = execute_source(&mut vm, "(VM _ModuleAt: 'Lib) pub")
            .expect("public lookup through module surface should work");
        assert!(value.is_fixnum());
        assert_eq!(unsafe { value.to_i64() }, 3);

        let err = execute_source(&mut vm, "(VM _ModuleAt: 'Lib) hidden")
            .expect_err("hidden lookup must fail");
        assert!(err.contains("MessageNotUnderstood"));
    }

    #[test]
    fn vm_exposes_platform_os_and_arch() {
        let mut vm = crate::special::bootstrap(HeapSettings::default());

        let os = execute_source(&mut vm, "VM _PlatformOS")
            .expect("platform os should evaluate");
        let arch = execute_source(&mut vm, "VM _PlatformArch")
            .expect("platform arch should evaluate");

        assert_eq!(
            as_string(os).as_deref(),
            Some(std::env::consts::OS),
            "OS primitive should match std::env::consts::OS"
        );
        assert_eq!(
            as_string(arch).as_deref(),
            Some(std::env::consts::ARCH),
            "ARCH primitive should match std::env::consts::ARCH"
        );
    }

    #[test]
    fn module_reuse_with_same_source_is_idempotent() {
        let mut vm = crate::special::bootstrap(HeapSettings::default());
        let value = execute_source(
            &mut vm,
            "VM _ModuleOpen: 'Core::Math. pi := 3. answer := 42. VM _ModuleExport: 'pi. VM _ModuleExport: 'answer. VM _ModuleOpen: 'App. VM _ModuleUse: 'Core::Math. VM _ModuleUse: 'Core::Math As: { answer = 'mathAnswer }. VM _ModuleOpen: 'Core::Math. VM _ModuleOpen: 'App. pi _FixnumAdd: mathAnswer",
        )
        .expect("reusing module imports should succeed");
        assert!(value.is_fixnum());
        assert_eq!(unsafe { value.to_i64() }, 45);
    }

    #[test]
    fn spawn_platform_runs_block_and_join_returns_value() {
        let mut vm = crate::special::bootstrap(HeapSettings::default());
        let value = execute_source(
            &mut vm,
            "thread := VM _SpawnPlatform: [ 40 _FixnumAdd: 2 ]. VM _ThreadJoin: thread",
        )
        .expect("spawned platform thread should return block result");
        assert!(value.is_fixnum());
        assert_eq!(unsafe { value.to_i64() }, 42);
    }

    #[test]
    fn thread_current_returns_fixnum_handle() {
        let mut vm = crate::special::bootstrap(HeapSettings::default());
        let value = execute_source(&mut vm, "VM _ThreadCurrent")
            .expect("thread current should evaluate");
        assert!(value.is_fixnum());
        assert!(unsafe { value.to_i64() } > 0);
    }

    #[test]
    fn thread_join_unknown_handle_is_error() {
        let mut vm = crate::special::bootstrap(HeapSettings::default());
        let err = execute_source(&mut vm, "VM _ThreadJoin: 999999")
            .expect_err("joining unknown handle should fail");
        assert!(err.contains("unknown platform thread handle"));
    }

    #[test]
    fn thread_park_for_millis_advances_monotonic_clock() {
        let mut vm = crate::special::bootstrap(HeapSettings::default());
        let value = execute_source(
            &mut vm,
            "a := VM _Millis. VM _ThreadParkForMillis: 10. b := VM _Millis. b _FixnumSub: a",
        )
        .expect("park-for-millis should return");
        assert!(value.is_fixnum());
        assert!(unsafe { value.to_i64() } >= 1);
    }

    #[test]
    fn unix_time_returns_positive_epoch_seconds() {
        let mut vm = crate::special::bootstrap(HeapSettings::default());
        let value = execute_source(&mut vm, "VM _UnixTime")
            .expect("unix time should evaluate");
        assert!(value.is_fixnum());
        assert!(unsafe { value.to_i64() } > 1_500_000_000);
    }

    #[test]
    fn thread_unpark_self_pregrant_makes_park_nonblocking() {
        let mut vm = crate::special::bootstrap(HeapSettings::default());
        let value = execute_source(
            &mut vm,
            "tok := VM _ThreadCurrent. VM _ThreadUnpark: tok. VM _ThreadPark. 7",
        )
        .expect("self unpark permit should release park");
        assert!(value.is_fixnum());
        assert_eq!(unsafe { value.to_i64() }, 7);
    }

    #[test]
    fn thread_unpark_unknown_token_returns_false() {
        let mut vm = crate::special::bootstrap(HeapSettings::default());
        let value = execute_source(&mut vm, "VM _ThreadUnpark: 999999")
            .expect("thread unpark on unknown token should not error");
        assert_eq!(value.raw(), vm.special.false_obj.raw());
    }

    #[test]
    fn core_thread_wrapper_spawn_and_join() {
        let mut vm = crate::special::bootstrap(HeapSettings::default());
        load_core_init(&mut vm);
        let value = execute_source(
            &mut vm,
            "t := Thread spawnPlatform: [ 40 _FixnumAdd: 2 ]. t join",
        )
        .expect("Thread wrapper should spawn and join");
        assert!(value.is_fixnum());
        assert_eq!(unsafe { value.to_i64() }, 42);
    }

    #[test]
    fn monitor_enter_exit_is_reentrant() {
        let mut vm = crate::special::bootstrap(HeapSettings::default());
        let value = execute_source(
            &mut vm,
            "lock := Object _Clone: Object. VM _MonitorEnter: lock. VM _MonitorEnter: lock. VM _MonitorExit: lock. VM _MonitorExit: lock. 7",
        )
        .expect("reentrant monitor enter/exit should succeed");
        assert!(value.is_fixnum());
        assert_eq!(unsafe { value.to_i64() }, 7);
    }

    #[test]
    fn monitor_exit_without_owner_is_error() {
        let mut vm = crate::special::bootstrap(HeapSettings::default());
        let err = execute_source(
            &mut vm,
            "lock := Object _Clone: Object. VM _MonitorExit: lock",
        )
        .expect_err("monitor exit without ownership should fail");
        assert!(err.contains("monitor exit without ownership"));
    }

    #[test]
    fn monitor_wait_without_owner_is_error() {
        let mut vm = crate::special::bootstrap(HeapSettings::default());
        let err = execute_source(
            &mut vm,
            "lock := Object _Clone: Object. VM _MonitorWait: lock",
        )
        .expect_err("monitor wait without ownership should fail");
        assert!(err.contains("monitor wait without ownership"));
    }

    #[test]
    fn core_reentrant_lock_reenters_and_unlocks() {
        let mut vm = crate::special::bootstrap(HeapSettings::default());
        load_core_init(&mut vm);
        let value = execute_source(
            &mut vm,
            "l := ReentrantLock new. l lock. l lock. l unlock. l unlock. 1",
        )
        .expect("ReentrantLock should allow reentry");
        assert!(value.is_fixnum());
        assert_eq!(unsafe { value.to_i64() }, 1);
    }

    #[test]
    fn core_synchronized_executes_body() {
        let mut vm = crate::special::bootstrap(HeapSettings::default());
        load_core_init(&mut vm);
        let value = execute_source(
            &mut vm,
            "obj := { parent* = Object. x := 0 }. obj synchronized: [ obj x: 42 ]. obj x",
        )
        .expect("synchronized: should execute block body");
        assert!(value.is_fixnum());
        assert_eq!(unsafe { value.to_i64() }, 42);
    }

    #[test]
    fn monitor_fast_path_uncontended_stays_thin() {
        let mut vm = crate::special::bootstrap(HeapSettings::default());
        let lock = execute_source(
            &mut vm,
            "lock := Object _Clone: Object. VM _MonitorEnter: lock. VM _MonitorExit: lock. lock",
        )
        .expect("monitor enter/exit should work");
        let header: &Header = unsafe { lock.as_ref() };
        assert_eq!(lock_state(header.flags_acquire().0), LOCK_STATE_UNLOCKED);

        let table = vm.lock_records.lock().expect("lock table poisoned");
        assert!(table.get(&lock.ref_bits()).is_none());
    }

    #[test]
    fn monitor_thin_owner_can_inflate_to_monitor() {
        let mut vm = crate::special::bootstrap(HeapSettings::default());
        let lock = execute_source(
            &mut vm,
            "LockObj := Object _Clone: Object. VM _MonitorEnter: LockObj. LockObj",
        )
        .expect("thin lock acquisition should succeed");
        let header: &Header = unsafe { lock.as_ref() };
        assert_eq!(lock_state(header.flags_acquire().0), LOCK_STATE_THIN);

        let token = threading::current_thread_token();
        let monitor = ensure_inflated_owned(&mut vm, lock, header, token)
            .expect("inflation should succeed");
        assert_eq!(lock_state(header.flags_acquire().0), LOCK_STATE_INFLATED);
        let guard = monitor.state.lock().expect("monitor state poisoned");
        assert_eq!(guard.owner, Some(token));
        assert_eq!(guard.recursion, 1);
        drop(guard);

        execute_source(&mut vm, "VM _MonitorExit: LockObj")
            .expect("inflated monitor exit should succeed");
    }

    #[test]
    fn monitor_cross_thread_contention_inflates_and_stays_inflated() {
        let mut vm = crate::special::bootstrap(HeapSettings::default());
        let lock = execute_source(
            &mut vm,
            "LockObj := Object _Clone: Object. VM _MonitorEnter: LockObj. LockObj",
        )
        .expect("cross-thread contention scenario should run");

        let lock_raw = lock.raw();
        let contender = std::thread::spawn(move || {
            let lock = Value::from_raw(lock_raw);
            let header: &Header = unsafe { lock.as_ref() };
            loop {
                let flags = header.flags_acquire().0;
                match lock_state(flags) {
                    LOCK_STATE_THIN => {
                        let next = with_lock_state(flags, LOCK_STATE_INFLATING);
                        if header
                            .compare_exchange_flags(
                                HeaderFlags(flags),
                                HeaderFlags(next),
                                Ordering::AcqRel,
                                Ordering::Acquire,
                            )
                            .is_ok()
                        {
                            return;
                        }
                    }
                    LOCK_STATE_INFLATING | LOCK_STATE_INFLATED => return,
                    _ => std::thread::yield_now(),
                }
            }
        });
        contender
            .join()
            .expect("contending thread should transition to inflating");

        execute_source(&mut vm, "VM _MonitorExit: LockObj")
            .expect("thin owner exit should complete inflation handoff");

        let header: &Header = unsafe { lock.as_ref() };
        assert_eq!(lock_state(header.flags_acquire().0), LOCK_STATE_INFLATED);

        execute_source(
            &mut vm,
            "VM _MonitorEnter: LockObj. VM _MonitorExit: LockObj. 0",
        )
        .expect("inflated lock should remain usable");
        assert_eq!(lock_state(header.flags_acquire().0), LOCK_STATE_INFLATED);
    }

    #[test]
    fn module_open_auto_uses_core_exports() {
        let mut vm = crate::special::bootstrap(HeapSettings::default());
        let value = execute_source(
            &mut vm,
            "VM _ModuleOpen: 'Core. Shared := 7. VM _ModuleExport: 'Shared. VM _ModuleOpen: 'App. Shared",
        )
        .expect("opening app should auto-use Core exports");
        assert!(value.is_fixnum());
        assert_eq!(unsafe { value.to_i64() }, 7);
    }

    #[test]
    fn module_assignment_through_import_updates_source_binding() {
        let mut vm = crate::special::bootstrap(HeapSettings::default());
        let value = execute_source(
            &mut vm,
            "VM _ModuleOpen: 'Lib. x := 1. VM _ModuleExport: 'x. VM _ModuleOpen: 'App. VM _ModuleUse: 'Lib. x := 9. VM _ModuleOpen: 'Lib. x",
        )
        .expect("assignment through imported symbol should write source");
        assert!(value.is_fixnum());
        assert_eq!(unsafe { value.to_i64() }, 9);
    }

    #[test]
    fn methods_resolve_globals_in_defining_module() {
        let mut vm = crate::special::bootstrap(HeapSettings::default());
        let value = execute_source(
            &mut vm,
            "VM _ModuleOpen: 'Lib. Posix := { O_RDONLY = 77 }. File := { open: path = { Posix O_RDONLY } }. VM _ModuleExport: 'File. VM _ModuleOpen: 'App. Posix := { O_RDONLY = 13 }. VM _ModuleUse: 'Lib. File open: \"x\"",
        )
        .expect("method global lookup should use defining module");
        assert!(value.is_fixnum());
        assert_eq!(unsafe { value.to_i64() }, 77);
    }

    #[test]
    #[ignore = "requires core/init method layer for high-level control flow"]
    fn keyword_args_survive_if_branch_with_object_literal() {
        let mut vm = crate::special::bootstrap(HeapSettings::default());
        let value = execute_source(
            &mut vm,
            "VM _ModuleOpen: 'App.
            Target := { f: a B: b C: c = { ^ ((a _FixnumAdd: b) _FixnumAdd: c) }. }.
            Broken := {
                test: a B: b C: c = {
                    ^ ({
                        parent* = Object.
                        value = (True ifTrue: [ Target f: a B: b C: c ] IfFalse: [ 0 ])
                    } value)
                }.
            }.
            Broken test: 1 B: 2 C: 3",
        )
        .expect("keyword args should remain intact through branch/object literal");
        assert!(value.is_fixnum());
        assert_eq!(unsafe { value.to_i64() }, 6);
    }

    #[test]
    fn qualified_export_reference_works_without_use() {
        let mut vm = crate::special::bootstrap(HeapSettings::default());
        let value = execute_source(
            &mut vm,
            "VM _ModuleOpen: 'Lib::Nested. Greeter := { greet = { 41 _FixnumAdd: 1 }. }. VM _ModuleExport: 'Greeter. VM _ModuleOpen: 'App. Lib::Nested::Greeter greet",
        )
        .expect("qualified export reference should resolve");
        assert!(value.is_fixnum());
        assert_eq!(unsafe { value.to_i64() }, 42);
    }

    #[test]
    fn qualified_export_assignment_is_rejected() {
        let mut vm = crate::special::bootstrap(HeapSettings::default());
        let err = execute_source(
            &mut vm,
            "VM _ModuleOpen: 'Lib::Nested. x := 1. VM _ModuleExport: 'x. VM _ModuleOpen: 'App. Lib::Nested::x := 3",
        )
        .expect_err("assignment to qualified export should fail");
        assert!(err.contains("cannot assign to qualified export"));
    }

    #[test]
    fn export_before_define_in_same_unit_works() {
        let mut vm = crate::special::bootstrap(HeapSettings::default());
        let value = execute_source(
            &mut vm,
            "VM _ModuleOpen: 'Lib. VM _ModuleExport: 'Hello. Hello := 42. VM _ModuleOpen: 'App. VM _ModuleUse: 'Lib. Hello",
        )
        .expect("export before define should resolve");
        assert!(value.is_fixnum());
        assert_eq!(unsafe { value.to_i64() }, 42);
    }

    #[test]
    fn forward_global_reference_in_same_unit_compiles() {
        let mut vm = crate::special::bootstrap(HeapSettings::default());
        let code = compile_source(
            &mut vm,
            "VM _ModuleOpen: 'App. Holder := { get = { x } }. x := 41.",
        )
        .expect("forward global reference should compile");
        assert!(code.constants.iter().any(|c| matches!(
            c,
            compiler0::ConstEntry::ModuleAssoc { module, name }
                if module == "App" && name == "x"
        )));
    }

    #[test]
    fn unresolved_global_is_compile_error() {
        let mut vm = crate::special::bootstrap(HeapSettings::default());
        let err = compile_source(&mut vm, "VM _ModuleOpen: 'App. missing")
            .expect_err("unresolved global should fail compile");
        assert!(err.contains("unresolved global 'missing'"));
    }

    #[test]
    fn module_compile_emits_module_assoc_constants() {
        let mut vm = crate::special::bootstrap(HeapSettings::default());
        execute_source(
            &mut vm,
            "VM _ModuleOpen: 'Lib. Hello := 1. VM _ModuleExport: 'Hello.",
        )
        .expect("setup lib module");

        let code = compile_source(
            &mut vm,
            "VM _ModuleOpen: 'App. VM _ModuleUse: 'Lib. Hello _FixnumAdd: 1",
        )
        .expect("compile should succeed");

        assert!(code.constants.iter().any(|c| matches!(
            c,
            compiler0::ConstEntry::ModuleAssoc { module, name }
                if module == "Lib" && name == "Hello"
        )));
    }

    #[test]
    fn high_level_module_export_exports_symbol_lists() {
        let mut vm = crate::special::bootstrap(HeapSettings::default());
        load_core_init(&mut vm);
        load_core_math(&mut vm);
        load_core_collections(&mut vm);

        execute_source(
            &mut vm,
            "Module open: 'M. A := 1. B := 2. Module export: ('A & 'B).",
        )
        .expect("high-level module export should execute");

        let entries = vm
            .module_public_entries("M")
            .expect("module M should exist");
        assert!(entries.iter().any(|(name, _)| name == "A"));
        assert!(entries.iter().any(|(name, _)| name == "B"));
    }

    #[test]
    fn high_level_module_use_imports_symbol_lists() {
        let mut vm = crate::special::bootstrap(HeapSettings::default());
        load_core_init(&mut vm);
        load_core_math(&mut vm);
        load_core_collections(&mut vm);

        execute_source(
            &mut vm,
            "VM _ModuleOpen: 'A. XA := 10. VM _ModuleExport: 'XA.",
        )
        .expect("setup module A");
        execute_source(
            &mut vm,
            "VM _ModuleOpen: 'B. YB := 32. VM _ModuleExport: 'YB.",
        )
        .expect("setup module B");

        let value = execute_source(
            &mut vm,
            "Module open: 'App. Module use: ('A & 'B). XA _FixnumAdd: YB",
        )
        .expect("high-level module use list should import both modules");
        assert!(value.is_fixnum());
        assert_eq!(unsafe { value.to_i64() }, 42);
    }

    #[test]
    fn collections_ampersand_builds_two_element_collector() {
        let mut vm = crate::special::bootstrap(HeapSettings::default());
        load_core_init(&mut vm);
        load_core_math(&mut vm);
        load_core_collections(&mut vm);

        let count_manual = execute_source(
            &mut vm,
            "c := Collector clone init. c add: 'A. c add: 'B. c count",
        )
        .expect("manual collector adds should work");
        assert!(count_manual.is_fixnum());
        assert_eq!(unsafe { count_manual.to_i64() }, 2);

        let count = execute_source(
            &mut vm,
            "c := Collector with: 'A With: 'B. c count",
        )
        .expect("collector with two values should work");
        assert!(count.is_fixnum());
        assert_eq!(unsafe { count.to_i64() }, 2);

        let size = execute_source(&mut vm, "('A & 'B) asArray size")
            .expect("ampersand collector expression should work");
        assert!(size.is_fixnum());
        assert_eq!(unsafe { size.to_i64() }, 2);
    }

    #[test]
    #[ignore = "performance comparison"]
    fn linked_list_chasing_ic_vs_no_ic() {
        let workload_path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../tests/linked_list_chasing.ktt");
        let workload = fs::read_to_string(workload_path)
            .expect("read tests/linked_list_chasing.ktt");

        let mut vm_with_ic = crate::special::bootstrap(HeapSettings::default());
        load_core_init(&mut vm_with_ic);
        load_core_math(&mut vm_with_ic);
        load_core_collections(&mut vm_with_ic);
        let with_ic_desc = compile_source(&mut vm_with_ic, &workload)
            .expect("compile with ic");
        let with_ic_code =
            materialize::materialize(&mut vm_with_ic, &with_ic_desc);

        let mut vm_without_ic =
            crate::special::bootstrap(HeapSettings::default());
        load_core_init(&mut vm_without_ic);
        load_core_math(&mut vm_without_ic);
        load_core_collections(&mut vm_without_ic);
        let without_ic_desc = compile_source(&mut vm_without_ic, &workload)
            .expect("compile without ic");
        let without_ic_code =
            materialize::materialize(&mut vm_without_ic, &without_ic_desc);
        unsafe {
            let code_ptr = without_ic_code.ref_bits() as *mut object::Code;
            (*code_ptr).feedback = vm_without_ic.special.none;
        }

        let warm_with = interpreter::interpret(&mut vm_with_ic, with_ic_code)
            .expect("warmup with ic");
        let warm_without =
            interpreter::interpret(&mut vm_without_ic, without_ic_code)
                .expect("warmup without ic");
        assert_eq!(warm_with.raw(), warm_without.raw());

        interpreter::ic_stats_reset();
        let start_with = Instant::now();
        let out_with = interpreter::interpret(&mut vm_with_ic, with_ic_code)
            .expect("run with ic");
        let elapsed_with = start_with.elapsed();
        let with_ic_stats = interpreter::ic_stats_snapshot();

        interpreter::ic_stats_reset();
        let start_without = Instant::now();
        let out_without =
            interpreter::interpret(&mut vm_without_ic, without_ic_code)
                .expect("run without ic");
        let elapsed_without = start_without.elapsed();
        let without_ic_stats = interpreter::ic_stats_snapshot();

        assert_eq!(out_with.raw(), out_without.raw());
        eprintln!(
            "linked-list-chasing: with_ic={:?}, without_ic={:?}, speedup={:.3}x",
            elapsed_with,
            elapsed_without,
            elapsed_without.as_secs_f64() / elapsed_with.as_secs_f64(),
        );
        eprintln!("IC stats with IC: {:?}", with_ic_stats);
        eprintln!("IC stats without IC: {:?}", without_ic_stats);
        assert!(
            with_ic_stats.mono_poly_hits + with_ic_stats.megamorphic_hits > 0,
            "expected IC fast-path hits in linked-list workload"
        );
    }
}
