use std::alloc::Layout;
use std::cell::RefCell;
use std::collections::HashMap;
use std::mem::size_of;
use std::ptr;
#[cfg(all(feature = "ic-cache", debug_assertions))]
use std::sync::atomic::{AtomicU64, Ordering};

use bytecode::{source_map_lookup, Instruction, Op};
use heap::{HeapProxy, RootProvider};
use object::{
    init_array, init_map, map_allocation_size, slot_object_allocation_size,
    Array, Block, Code, Header, Map, ObjectType, Slot, SlotFlags, SlotObject,
    VMSymbol, Value,
};

use crate::VM;

const MAX_FRAMES: usize = 1024;
const MAX_POLYMORPHIC_FEEDBACK_ENTRIES: usize = 4;
const MEGAMORPHIC_CACHE_SIZE: usize = 1024;
const MEGAMORPHIC_CACHE_MASK: usize = MEGAMORPHIC_CACHE_SIZE - 1;
const FEEDBACK_ENTRY_STRIDE: usize = 5;
const FEEDBACK_ENTRY_MAP_IDX: usize = 0;
const FEEDBACK_ENTRY_HOLDER_IDX: usize = 1;
const FEEDBACK_ENTRY_HOLDER_MAP_IDX: usize = 2;
const FEEDBACK_ENTRY_SLOT_INDEX_IDX: usize = 3;
const FEEDBACK_ENTRY_HOLDER_IS_RECEIVER_IDX: usize = 4;

#[derive(Clone, Copy, PartialEq, Eq)]
struct MegamorphicKey {
    message_raw: u64,
    receiver_map_raw: u64,
    holder_raw: u64,
    delegate_raw: u64,
}

impl MegamorphicKey {
    fn hash(self) -> u64 {
        let mut x = self.message_raw.rotate_left(13)
            ^ self.receiver_map_raw.rotate_left(29)
            ^ self.holder_raw.rotate_left(7)
            ^ self.delegate_raw.rotate_left(43);
        x ^= x >> 33;
        x = x.wrapping_mul(0xff51afd7ed558ccd);
        x ^= x >> 33;
        x = x.wrapping_mul(0xc4ceb9fe1a85ec53);
        x ^ (x >> 33)
    }
}

#[derive(Clone, Copy)]
struct MegamorphicEntry {
    key: MegamorphicKey,
    holder_raw: u64,
    holder_map_raw: u64,
    slot_index: u32,
    holder_is_receiver: bool,
}

struct MegamorphicCache {
    epoch: u8,
    entries: Vec<Option<MegamorphicEntry>>,
}

impl MegamorphicCache {
    fn new() -> Self {
        Self {
            epoch: 0,
            entries: vec![None; MEGAMORPHIC_CACHE_SIZE],
        }
    }
}

thread_local! {
    static MEGAMORPHIC_CACHE: RefCell<MegamorphicCache> = RefCell::new(MegamorphicCache::new());
}

const IC_CACHE_ENABLED: bool = cfg!(feature = "ic-cache");

#[cfg(all(feature = "ic-cache", debug_assertions))]
static IC_MONO_POLY_HITS: AtomicU64 = AtomicU64::new(0);
#[cfg(all(feature = "ic-cache", debug_assertions))]
static IC_MEGAMORPHIC_HITS: AtomicU64 = AtomicU64::new(0);
#[cfg(all(feature = "ic-cache", debug_assertions))]
static IC_UPDATES: AtomicU64 = AtomicU64::new(0);
#[cfg(all(feature = "ic-cache", debug_assertions))]
static IC_MISSES: AtomicU64 = AtomicU64::new(0);

#[derive(Debug, Clone, Copy)]
pub struct IcStats {
    pub mono_poly_hits: u64,
    pub megamorphic_hits: u64,
    pub updates: u64,
    pub misses: u64,
}

#[cfg(all(feature = "ic-cache", debug_assertions))]
pub fn ic_stats_reset() {
    IC_MONO_POLY_HITS.store(0, Ordering::Relaxed);
    IC_MEGAMORPHIC_HITS.store(0, Ordering::Relaxed);
    IC_UPDATES.store(0, Ordering::Relaxed);
    IC_MISSES.store(0, Ordering::Relaxed);
}

#[cfg(not(all(feature = "ic-cache", debug_assertions)))]
pub fn ic_stats_reset() {}

#[cfg(all(feature = "ic-cache", debug_assertions))]
pub fn ic_stats_snapshot() -> IcStats {
    IcStats {
        mono_poly_hits: IC_MONO_POLY_HITS.load(Ordering::Relaxed),
        megamorphic_hits: IC_MEGAMORPHIC_HITS.load(Ordering::Relaxed),
        updates: IC_UPDATES.load(Ordering::Relaxed),
        misses: IC_MISSES.load(Ordering::Relaxed),
    }
}

#[cfg(not(all(feature = "ic-cache", debug_assertions)))]
pub fn ic_stats_snapshot() -> IcStats {
    IcStats {
        mono_poly_hits: 0,
        megamorphic_hits: 0,
        updates: 0,
        misses: 0,
    }
}

#[inline]
fn ic_count_mono_poly_hit() {
    #[cfg(all(feature = "ic-cache", debug_assertions))]
    IC_MONO_POLY_HITS.fetch_add(1, Ordering::Relaxed);
}

#[inline]
fn ic_count_megamorphic_hit() {
    #[cfg(all(feature = "ic-cache", debug_assertions))]
    IC_MEGAMORPHIC_HITS.fetch_add(1, Ordering::Relaxed);
}

#[inline]
fn ic_count_update() {
    #[cfg(all(feature = "ic-cache", debug_assertions))]
    IC_UPDATES.fetch_add(1, Ordering::Relaxed);
}

#[inline]
fn ic_count_miss() {
    #[cfg(all(feature = "ic-cache", debug_assertions))]
    IC_MISSES.fetch_add(1, Ordering::Relaxed);
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RuntimeError {
    MessageNotUnderstood { receiver: Value, message: Value },
    UnhandledSignal { condition: Value },
    NonLocalReturnExpired,
    UnwindWithoutHandler,
    StackOverflow,
    TypeError { expected: &'static str, got: Value },
    Unimplemented { message: &'static str },
    UndefinedGlobal { name: String },
}

#[derive(Debug, Clone, Copy)]
pub struct SourceRange {
    pub start: u32,
    pub end: u32,
}

#[derive(Debug, Clone)]
pub struct LocatedRuntimeError {
    pub error: RuntimeError,
    pub location: Option<SourceRange>,
}

#[derive(Debug, Clone)]
struct Frame {
    code: Value,
    pc: usize,
    reg_base: usize,
    reg_len: usize,
    temp_array: Value,
    is_block: bool,
    method_frame_idx: usize,
    holder: Value,
    holder_slot_index: u32,
    module_path: Option<String>,
    module_dynamic: bool,
}

#[derive(Debug, Clone, Copy)]
struct HandlerScope {
    scope_depth: usize,
    handler: Value,
}

#[derive(Debug, Clone, Copy)]
struct FinalizerScope {
    scope_depth: usize,
    cleanup: Value,
}

#[derive(Debug, Clone, Copy)]
struct PendingRestore {
    return_depth: usize,
    value: Value,
}

#[derive(Debug, Clone, Copy)]
struct UnwindState {
    target_depth: usize,
    value: Value,
}

pub struct InterpreterState {
    acc: Value,
    frames: Vec<Frame>,
    register_stack: Vec<Value>,
    register_top: usize,
    handlers: Vec<HandlerScope>,
    finalizers: Vec<FinalizerScope>,
    pending_restores: Vec<PendingRestore>,
    unwind_cleanup_depths: Vec<usize>,
    unwind: Option<UnwindState>,
    last_pc: usize,
    last_code: Value,
}

pub(crate) struct InterpreterRoots<'a> {
    state: &'a mut InterpreterState,
    pub(crate) special: &'a mut object::SpecialObjects,
    intern_table: &'a mut HashMap<String, Value>,
    pub(crate) assoc_map: &'a mut Value,
    pub(crate) dictionary: &'a mut Value,
    modules: &'a mut HashMap<String, crate::ModuleState>,
    pub(crate) scratch: &'a mut Vec<Value>,
}

impl RootProvider for InterpreterRoots<'_> {
    fn visit_roots(&mut self, visitor: &mut dyn FnMut(&mut Value)) {
        visitor(&mut self.state.acc);
        for frame in self.state.frames.iter_mut() {
            visitor(&mut frame.code);
            visitor(&mut frame.temp_array);
            visitor(&mut frame.holder);
            for i in 0..frame.reg_len {
                let reg = &mut self.state.register_stack[frame.reg_base + i];
                visitor(reg);
            }
        }
        for handler in self.state.handlers.iter_mut() {
            visitor(&mut handler.handler);
        }
        for finalizer in self.state.finalizers.iter_mut() {
            visitor(&mut finalizer.cleanup);
        }
        for restore in self.state.pending_restores.iter_mut() {
            visitor(&mut restore.value);
        }
        if let Some(unwind) = self.state.unwind.as_mut() {
            visitor(&mut unwind.value);
        }
        visitor(&mut self.special.none);
        visitor(&mut self.special.true_obj);
        visitor(&mut self.special.false_obj);
        visitor(&mut self.special.map_map);
        visitor(&mut self.special.object);
        visitor(&mut self.special.block_traits);
        visitor(&mut self.special.array_traits);
        visitor(&mut self.special.bytearray_traits);
        visitor(&mut self.special.bignum_traits);
        visitor(&mut self.special.alien_traits);
        visitor(&mut self.special.string_traits);
        visitor(&mut self.special.symbol_traits);
        visitor(&mut self.special.ratio_traits);
        visitor(&mut self.special.fixnum_traits);
        visitor(&mut self.special.code_traits);
        visitor(&mut self.special.float_traits);
        visitor(self.assoc_map);
        visitor(self.dictionary);
        for module in self.modules.values_mut() {
            for value in module.bindings.values_mut() {
                visitor(value);
            }
        }
        for v in self.intern_table.values_mut() {
            visitor(v);
        }
        for v in self.scratch.iter_mut() {
            visitor(v);
        }
    }
}

pub fn interpret(
    vm: &mut VM,
    code: Value,
) -> Result<Value, LocatedRuntimeError> {
    interpret_with_receiver(vm, code, vm.special.none)
}

pub fn interpret_with_receiver(
    vm: &mut VM,
    code: Value,
    receiver: Value,
) -> Result<Value, LocatedRuntimeError> {
    let mut state = InterpreterState {
        acc: vm.special.none,
        frames: Vec::new(),
        register_stack: Vec::new(),
        register_top: 0,
        handlers: Vec::new(),
        finalizers: Vec::new(),
        pending_restores: Vec::new(),
        unwind_cleanup_depths: Vec::new(),
        unwind: None,
        last_pc: 0,
        last_code: code,
    };

    push_entry_frame(vm, &mut state, code, receiver)
        .map_err(|e| locate_error(e, &state))?;
    run(vm, &mut state).map_err(|e| locate_error(e, &state))
}

fn locate_error(
    error: RuntimeError,
    state: &InterpreterState,
) -> LocatedRuntimeError {
    let location = if state.last_code.is_ref() {
        let code: &Code = unsafe { state.last_code.as_ref() };
        let source_map = unsafe { code.source_map() };
        source_map_lookup(source_map, state.last_pc as u32)
            .map(|(start, end)| SourceRange { start, end })
    } else {
        None
    };
    LocatedRuntimeError { error, location }
}

fn run(
    vm: &mut VM,
    state: &mut InterpreterState,
) -> Result<Value, RuntimeError> {
    loop {
        if process_control(vm, state)? {
            continue;
        }

        let Some(frame_idx) = current_frame_index(state) else {
            return Ok(state.acc);
        };

        let (instr, code_val) = {
            let frame = &mut state.frames[frame_idx];
            state.last_pc = frame.pc;
            state.last_code = frame.code;
            let code: &Code = unsafe { frame.code.as_ref() };
            let bytecode = unsafe { code.bytecode() };
            let (instr, next_pc) = decode_at(bytecode, frame.pc);
            frame.pc = next_pc;
            (instr, frame.code)
        };

        match instr {
            Instruction::LoadConstant { idx } => {
                let code: &Code = unsafe { code_val.as_ref() };
                let value = unsafe { code.constant(idx as u32) };
                state.acc = value;
            }
            Instruction::LoadSmi { value } => {
                state.acc = Value::from_i64(value as i64);
            }
            Instruction::LoadLocal { reg } => {
                state.acc = get_register(state, frame_idx, reg)?;
            }
            Instruction::StoreLocal { reg } => {
                let value = state.acc;
                set_register(state, frame_idx, reg, value)?;
            }
            Instruction::Mov { dst, src } => {
                let value = get_register(state, frame_idx, src)?;
                set_register(state, frame_idx, dst, value)?;
            }
            Instruction::LoadStack { offset } => {
                let none = vm.special.none;
                state.acc = load_stack_slot(state, frame_idx, offset, none);
            }
            Instruction::StoreStack { offset } => {
                let value = state.acc;
                let none = vm.special.none;
                store_stack_slot(state, frame_idx, offset, value, none);
            }
            Instruction::MovToStack { offset, src } => {
                let value = get_register(state, frame_idx, src)?;
                let none = vm.special.none;
                store_stack_slot(state, frame_idx, offset, value, none);
            }
            Instruction::MovFromStack { dst, offset } => {
                let none = vm.special.none;
                let value = load_stack_slot(state, frame_idx, offset, none);
                set_register(state, frame_idx, dst, value)?;
            }
            Instruction::LoadTemp { array_idx, idx } => {
                let value = load_temp(vm, state, frame_idx, array_idx, idx)?;
                state.acc = value;
            }
            Instruction::StoreTemp { array_idx, idx } => {
                let value = state.acc;
                store_temp(vm, state, frame_idx, array_idx, idx, value)?;
            }
            Instruction::MovToTemp {
                array_idx,
                idx,
                src,
            } => {
                let value = get_register(state, frame_idx, src)?;
                store_temp(vm, state, frame_idx, array_idx, idx, value)?;
            }
            Instruction::MovFromTemp {
                dst,
                array_idx,
                idx,
            } => {
                let value = load_temp(vm, state, frame_idx, array_idx, idx)?;
                set_register(state, frame_idx, dst, value)?;
            }
            Instruction::LoadAssoc { idx } => {
                let value = load_assoc(vm, code_val, idx)?;
                state.acc = value;
            }
            Instruction::StoreAssoc { idx } => {
                let value = state.acc;
                store_assoc(vm, code_val, idx, value)?;
            }
            Instruction::MovToAssoc { idx, src } => {
                let value = get_register(state, frame_idx, src)?;
                store_assoc(vm, code_val, idx, value)?;
            }
            Instruction::MovFromAssoc { dst, idx } => {
                let value = load_assoc(vm, code_val, idx)?;
                set_register(state, frame_idx, dst, value)?;
            }
            Instruction::CreateObject {
                map_idx,
                values_reg,
            } => {
                let obj = create_object(
                    vm, state, frame_idx, code_val, map_idx, values_reg,
                )?;
                state.acc = obj;
            }
            Instruction::CreateBlock { block_idx } => {
                let block = create_block(vm, state, code_val, block_idx)?;
                state.acc = block;
            }
            Instruction::Send {
                message_idx,
                reg,
                argc,
                feedback_idx,
            } => {
                dispatch_send(
                    vm,
                    state,
                    frame_idx,
                    code_val,
                    message_idx,
                    reg,
                    argc,
                    feedback_idx,
                )?;
            }
            Instruction::Resend {
                message_idx,
                reg,
                argc,
                feedback_idx,
            } => {
                dispatch_resend(
                    vm,
                    state,
                    frame_idx,
                    code_val,
                    message_idx,
                    reg,
                    argc,
                    feedback_idx,
                    None,
                )?;
            }
            Instruction::DirectedResend {
                message_idx,
                reg,
                argc,
                feedback_idx,
                delegate_idx,
            } => {
                dispatch_resend(
                    vm,
                    state,
                    frame_idx,
                    code_val,
                    message_idx,
                    reg,
                    argc,
                    feedback_idx,
                    Some(delegate_idx),
                )?;
            }
            Instruction::Jump { offset } => {
                let frame = &mut state.frames[frame_idx];
                frame.pc = jump_target(frame.pc, offset)?;
            }
            Instruction::JumpIfTrue { offset } => {
                if is_truthy(vm, state.acc) {
                    let frame = &mut state.frames[frame_idx];
                    frame.pc = jump_target(frame.pc, offset)?;
                }
            }
            Instruction::JumpIfFalse { offset } => {
                if !is_truthy(vm, state.acc) {
                    let frame = &mut state.frames[frame_idx];
                    frame.pc = jump_target(frame.pc, offset)?;
                }
            }
            Instruction::LocalReturn => {
                pop_frame(state);
            }
            Instruction::Return => {
                let method_idx = state.frames[frame_idx].method_frame_idx;
                if method_idx >= state.frames.len() {
                    return Err(RuntimeError::NonLocalReturnExpired);
                }
                truncate_frames(state, method_idx);
            }
        }
    }
}

fn process_control(
    vm: &mut VM,
    state: &mut InterpreterState,
) -> Result<bool, RuntimeError> {
    if let Some(&depth) = state.unwind_cleanup_depths.last() {
        if state.frames.len() > depth {
            return Ok(false);
        }
        state.unwind_cleanup_depths.pop();
    }

    while let Some(restore) = state.pending_restores.last().copied() {
        if state.frames.len() == restore.return_depth {
            state.acc = restore.value;
            state.pending_restores.pop();
            continue;
        }
        break;
    }

    let frame_depth = state.frames.len();
    while state
        .handlers
        .last()
        .is_some_and(|scope| frame_depth <= scope.scope_depth)
    {
        state.handlers.pop();
    }

    if let Some(unwind) = state.unwind {
        if run_due_finalizer(vm, state, false)? {
            return Ok(true);
        }
        if frame_depth > unwind.target_depth {
            pop_frame(state);
            return Ok(true);
        }
        if frame_depth == unwind.target_depth {
            state.acc = unwind.value;
            state.unwind = None;
            return Ok(true);
        }
        return Err(RuntimeError::NonLocalReturnExpired);
    }

    if run_due_finalizer(vm, state, true)? {
        return Ok(true);
    }

    Ok(false)
}

fn run_due_finalizer(
    vm: &mut VM,
    state: &mut InterpreterState,
    preserve_acc: bool,
) -> Result<bool, RuntimeError> {
    let frame_depth = state.frames.len();
    if !state
        .finalizers
        .last()
        .is_some_and(|scope| frame_depth <= scope.scope_depth)
    {
        return Ok(false);
    }

    let finalizer = state.finalizers.pop().expect("checked non-empty");
    if preserve_acc {
        state.pending_restores.push(PendingRestore {
            return_depth: frame_depth,
            value: state.acc,
        });
    } else {
        state.unwind_cleanup_depths.push(frame_depth);
    }
    call_block(vm, state, finalizer.cleanup, &[])?;
    Ok(true)
}

fn push_entry_frame(
    vm: &mut VM,
    state: &mut InterpreterState,
    code: Value,
    receiver: Value,
) -> Result<(), RuntimeError> {
    push_method_frame(
        vm,
        state,
        code,
        receiver,
        None,
        vm.special.none,
        0,
        None,
        true,
    )
}

fn push_method_frame(
    vm: &mut VM,
    state: &mut InterpreterState,
    code_val: Value,
    receiver: Value,
    args_source: Option<(usize, u16, u8)>,
    holder: Value,
    holder_slot_index: u32,
    module_path: Option<String>,
    module_dynamic: bool,
) -> Result<(), RuntimeError> {
    if state.frames.len() >= MAX_FRAMES {
        return Err(RuntimeError::StackOverflow);
    }

    let code = unsafe { &*expect_code(code_val)? };
    let arg_count = code.arg_count() as usize;
    let provided = args_source.map(|(_, _, argc)| argc as usize).unwrap_or(0);
    if provided != arg_count {
        return Err(RuntimeError::TypeError {
            expected: "argument count",
            got: Value::from_i64(provided as i64),
        });
    }

    let reg_count = code.register_count() as usize;
    let none = vm.special.none;
    let (reg_base, reg_len) = alloc_frame_registers(state, reg_count, none);
    unsafe { write_register_unchecked(state, reg_base, 0, receiver) };

    let temp_array = if code.temp_count() > 0 {
        state.acc = receiver;
        alloc_temp_array(vm, state, code.temp_count(), none)?
    } else {
        none
    };

    if let Some((src_idx, reg, argc)) = args_source {
        copy_args_from_frame(state, src_idx, reg, argc, reg_base, reg_len)?;
    }

    let method_frame_idx = state.frames.len();
    state.frames.push(Frame {
        code: code_val,
        pc: 0,
        reg_base,
        reg_len,
        temp_array,
        is_block: false,
        method_frame_idx,
        holder,
        holder_slot_index,
        module_path,
        module_dynamic,
    });

    Ok(())
}

fn push_block_frame_with_args(
    vm: &mut VM,
    state: &mut InterpreterState,
    code_val: Value,
    receiver: Value,
    args: &[Value],
    parent_env: Value,
    module_path: Option<String>,
    module_dynamic: bool,
) -> Result<(), RuntimeError> {
    if state.frames.len() >= MAX_FRAMES {
        return Err(RuntimeError::StackOverflow);
    }

    let code = unsafe { &*expect_code(code_val)? };
    let arg_count = code.arg_count() as usize;
    if args.len() != arg_count {
        return Err(RuntimeError::TypeError {
            expected: "argument count",
            got: Value::from_i64(args.len() as i64),
        });
    }

    let reg_count = code.register_count() as usize;
    let none = vm.special.none;
    let (reg_base, reg_len) = alloc_frame_registers(state, reg_count, none);
    unsafe { write_register_unchecked(state, reg_base, 0, receiver) };
    for (i, arg) in args.iter().enumerate() {
        let idx = i + 1;
        if idx < reg_len {
            unsafe { write_register_unchecked(state, reg_base, idx, *arg) };
        }
    }

    let temp_array = if code.temp_count() > 0 {
        state.acc = receiver;
        alloc_temp_array(vm, state, code.temp_count(), parent_env)?
    } else {
        parent_env
    };

    let method_frame_idx = state.frames.len();
    state.frames.push(Frame {
        code: code_val,
        pc: 0,
        reg_base,
        reg_len,
        temp_array,
        is_block: true,
        method_frame_idx,
        holder: vm.special.none,
        holder_slot_index: 0,
        module_path,
        module_dynamic,
    });

    Ok(())
}

fn feedback_map_for_receiver(
    vm: &VM,
    receiver: Value,
) -> Result<Value, RuntimeError> {
    if receiver.is_fixnum() {
        return Ok(vm.special.fixnum_traits);
    }
    let header: &Header = unsafe { receiver.as_ref() };
    let map = match header.object_type() {
        ObjectType::Slots => {
            let obj: &SlotObject = unsafe { receiver.as_ref() };
            obj.map
        }
        ObjectType::Block => vm.special.block_traits,
        ObjectType::Map => receiver,
        ObjectType::Array => vm.special.array_traits,
        ObjectType::ByteArray => vm.special.bytearray_traits,
        ObjectType::Str => vm.special.string_traits,
        ObjectType::Symbol => vm.special.symbol_traits,
        ObjectType::BigNum => vm.special.bignum_traits,
        ObjectType::Alien => vm.special.alien_traits,
        ObjectType::Ratio => vm.special.ratio_traits,
        ObjectType::Code => vm.special.code_traits,
        ObjectType::Float => vm.special.float_traits,
    };
    Ok(map)
}

fn decode_feedback_entries(entry: Value) -> Option<(*const Array, usize)> {
    if !entry.is_ref() {
        return None;
    }
    let header: &Header = unsafe { entry.as_ref() };
    if header.object_type() != ObjectType::Array {
        return None;
    }
    let array: &Array = unsafe { entry.as_ref() };
    let len = array.len() as usize;
    if len == 0 {
        return Some((array as *const Array, 0));
    }
    if len % FEEDBACK_ENTRY_STRIDE != 0 {
        return None;
    }
    let count = len / FEEDBACK_ENTRY_STRIDE;
    Some((array as *const Array, count))
}

fn decode_feedback_vector(entry: Value) -> Option<*const Array> {
    if !entry.is_ref() {
        return None;
    }
    // let header: &Header = unsafe { entry.as_ref() };
    // if header.object_type() != ObjectType::Array {
    //     return None;
    // }
    let array: &Array = unsafe { entry.as_ref() };
    Some(array as *const Array)
}

fn array_entry_at(array_ptr: *const Array, index: usize) -> Value {
    let array = unsafe { &*array_ptr };
    unsafe { array.element(index as u64) }
}

fn array_set_entry(vm: &mut VM, array_val: Value, index: usize, value: Value) {
    unsafe {
        let array_ptr = array_val.ref_bits() as *mut Array;
        let elems = array_ptr.add(1) as *mut Value;
        *elems.add(index) = value;
    }
    if value.is_ref() {
        vm.heap_proxy.write_barrier(array_val, value);
    }
}

#[inline(always)]
fn decode_fixnum_i64_unchecked(value: Value) -> i64 {
    debug_assert!(value.is_fixnum());
    unsafe { value.to_i64() }
}

#[inline(always)]
fn decode_cached_slot_index(value: Value) -> u32 {
    let raw = decode_fixnum_i64_unchecked(value);
    debug_assert!(raw >= 0 && raw <= u32::MAX as i64);
    raw as u32
}

#[inline(always)]
fn decode_cached_bool(value: Value) -> bool {
    decode_fixnum_i64_unchecked(value) != 0
}

fn megamorphic_key_for_send(
    message: Value,
    receiver_feedback_map: Value,
) -> MegamorphicKey {
    MegamorphicKey {
        message_raw: message.raw(),
        receiver_map_raw: receiver_feedback_map.raw(),
        holder_raw: 0,
        delegate_raw: 0,
    }
}

fn megamorphic_key_for_resend(
    message: Value,
    receiver_feedback_map: Value,
    holder: Value,
    delegate_name: Option<Value>,
) -> MegamorphicKey {
    MegamorphicKey {
        message_raw: message.raw(),
        receiver_map_raw: receiver_feedback_map.raw(),
        holder_raw: holder.raw(),
        delegate_raw: delegate_name.map(Value::raw).unwrap_or(0),
    }
}

fn megamorphic_cache_get(
    vm: &VM,
    key: MegamorphicKey,
) -> Option<MegamorphicEntry> {
    let current_epoch = vm.heap_proxy.epoch;
    MEGAMORPHIC_CACHE.with(|cache| {
        let mut cache = cache.borrow_mut();
        if cache.epoch != current_epoch {
            cache.entries.fill(None);
            cache.epoch = current_epoch;
        }
        let idx = (key.hash() as usize) & MEGAMORPHIC_CACHE_MASK;
        let entry = cache.entries[idx]?;
        if entry.key == key {
            Some(entry)
        } else {
            None
        }
    })
}

fn megamorphic_cache_put(vm: &VM, entry: MegamorphicEntry) {
    let current_epoch = vm.heap_proxy.epoch;
    MEGAMORPHIC_CACHE.with(|cache| {
        let mut cache = cache.borrow_mut();
        if cache.epoch != current_epoch {
            cache.entries.fill(None);
            cache.epoch = current_epoch;
        }
        let idx = (entry.key.hash() as usize) & MEGAMORPHIC_CACHE_MASK;
        cache.entries[idx] = Some(entry);
    });
}

fn try_dispatch_cached_handler(
    vm: &mut VM,
    state: &mut InterpreterState,
    frame_idx: usize,
    receiver: Value,
    holder: Value,
    cached_holder_map: Value,
    holder_is_receiver: bool,
    slot_index: u32,
    reg: u16,
    argc: u8,
) -> Result<bool, RuntimeError> {
    let holder_for_dispatch =
        if holder_is_receiver { receiver } else { holder };
    let holder_map_val = holder_map(holder_for_dispatch)?;
    if holder_map_val.raw() != cached_holder_map.raw() {
        return Ok(false);
    }

    let holder_map_obj: &Map = unsafe { holder_map_val.as_ref() };
    if slot_index >= holder_map_obj.slot_count() {
        return Ok(false);
    }
    let canonical_slot = unsafe { holder_map_obj.slot(slot_index) };
    let slot_value = if canonical_slot.is_assignable() {
        let offset = unsafe { canonical_slot.value.to_i64() } as u32;
        read_holder_value(holder_for_dispatch, offset)?
    } else {
        canonical_slot.value
    };
    let slot =
        Slot::new(canonical_slot.flags(), canonical_slot.name, slot_value);

    dispatch_slot(
        vm,
        state,
        frame_idx,
        receiver,
        holder_for_dispatch,
        slot,
        slot_index,
        reg,
        argc,
    )?;
    Ok(true)
}

fn try_dispatch_feedback_entry(
    vm: &mut VM,
    state: &mut InterpreterState,
    frame_idx: usize,
    code: &Code,
    feedback_idx: u16,
    megamorphic_key: MegamorphicKey,
    receiver: Value,
    receiver_feedback_map: Value,
    reg: u16,
    argc: u8,
) -> Result<bool, RuntimeError> {
    let feedback = code.feedback;
    if feedback.raw() == vm.special.none.raw() {
        return Ok(false);
    }
    let Some(vector) = decode_feedback_vector(feedback) else {
        return Ok(false);
    };
    let vector_len = unsafe { (&*vector).len() as usize };
    if feedback_idx as usize >= vector_len {
        return Ok(false);
    }
    let entry = array_entry_at(vector, feedback_idx as usize);
    if entry.raw() == vm.special.none.raw() {
        return Ok(false);
    }

    let Some((entries, entry_count)) = decode_feedback_entries(entry) else {
        return Ok(false);
    };

    if entry_count == 0 {
        if let Some(megamorphic) = megamorphic_cache_get(vm, megamorphic_key) {
            let hit = try_dispatch_cached_handler(
                vm,
                state,
                frame_idx,
                receiver,
                Value::from_raw(megamorphic.holder_raw),
                Value::from_raw(megamorphic.holder_map_raw),
                megamorphic.holder_is_receiver,
                megamorphic.slot_index,
                reg,
                argc,
            );
            if matches!(hit, Ok(true)) {
                ic_count_megamorphic_hit();
            }
            return hit;
        }
        return Ok(false);
    }

    for i in 0..entry_count {
        let base = i * FEEDBACK_ENTRY_STRIDE;
        let cached_map = array_entry_at(entries, base + FEEDBACK_ENTRY_MAP_IDX);
        if cached_map.raw() != receiver_feedback_map.raw() {
            continue;
        }

        let holder = array_entry_at(entries, base + FEEDBACK_ENTRY_HOLDER_IDX);
        let cached_holder_map =
            array_entry_at(entries, base + FEEDBACK_ENTRY_HOLDER_MAP_IDX);

        let slot_index_val =
            array_entry_at(entries, base + FEEDBACK_ENTRY_SLOT_INDEX_IDX);
        let slot_index = decode_cached_slot_index(slot_index_val);

        let holder_is_receiver_val = array_entry_at(
            entries,
            base + FEEDBACK_ENTRY_HOLDER_IS_RECEIVER_IDX,
        );
        let holder_is_receiver = decode_cached_bool(holder_is_receiver_val);

        if try_dispatch_cached_handler(
            vm,
            state,
            frame_idx,
            receiver,
            holder,
            cached_holder_map,
            holder_is_receiver,
            slot_index,
            reg,
            argc,
        )? {
            ic_count_mono_poly_hit();
            return Ok(true);
        }
    }

    Ok(false)
}

fn update_send_feedback_entry(
    vm: &mut VM,
    state: &mut InterpreterState,
    code: &Code,
    feedback_idx: u16,
    megamorphic_key: MegamorphicKey,
    receiver: Value,
    receiver_feedback_map: Value,
    holder: Value,
    slot_index: u32,
    traversed_assignable_parent: bool,
) -> Result<(), RuntimeError> {
    if traversed_assignable_parent {
        return Ok(());
    }
    let feedback = code.feedback;
    if feedback.raw() == vm.special.none.raw() {
        return Ok(());
    }
    let Some(vector) = decode_feedback_vector(feedback) else {
        return Ok(());
    };
    let vector_len = unsafe { (&*vector).len() as usize };
    if feedback_idx as usize >= vector_len {
        return Ok(());
    }

    let holder_feedback_map = holder_map(holder)?;
    let new_entry_values = [
        receiver_feedback_map,
        holder,
        holder_feedback_map,
        Value::from_i64(slot_index as i64),
        Value::from_i64((holder.raw() == receiver.raw()) as i64),
    ];

    let slot_entry = array_entry_at(vector, feedback_idx as usize);
    if slot_entry.raw() == vm.special.none.raw() {
        let mut scratch = Vec::new();
        let new_entry =
            with_roots(vm, state, &mut scratch, |proxy, roots| unsafe {
                crate::alloc::alloc_array(proxy, roots, &new_entry_values)
                    .value()
            });
        array_set_entry(vm, feedback, feedback_idx as usize, new_entry);
        ic_count_update();
        return Ok(());
    }

    let Some((entries, entry_count)) = decode_feedback_entries(slot_entry)
    else {
        return Ok(());
    };

    if entry_count == 0 {
        megamorphic_cache_put(
            vm,
            MegamorphicEntry {
                key: megamorphic_key,
                holder_raw: holder.raw(),
                holder_map_raw: holder_feedback_map.raw(),
                slot_index,
                holder_is_receiver: holder.raw() == receiver.raw(),
            },
        );
        ic_count_update();
        return Ok(());
    }

    for i in 0..entry_count {
        let base = i * FEEDBACK_ENTRY_STRIDE;
        let cached_map = array_entry_at(entries, base + FEEDBACK_ENTRY_MAP_IDX);
        if cached_map.raw() != receiver_feedback_map.raw() {
            continue;
        }
        for (offset, value) in new_entry_values.iter().enumerate() {
            array_set_entry(vm, slot_entry, base + offset, *value);
        }
        ic_count_update();
        return Ok(());
    }

    if entry_count >= MAX_POLYMORPHIC_FEEDBACK_ENTRIES {
        let mut scratch = Vec::new();
        let megamorphic_sentinel =
            with_roots(vm, state, &mut scratch, |proxy, roots| unsafe {
                crate::alloc::alloc_array(proxy, roots, &[]).value()
            });
        array_set_entry(
            vm,
            feedback,
            feedback_idx as usize,
            megamorphic_sentinel,
        );
        megamorphic_cache_put(
            vm,
            MegamorphicEntry {
                key: megamorphic_key,
                holder_raw: holder.raw(),
                holder_map_raw: holder_feedback_map.raw(),
                slot_index,
                holder_is_receiver: holder.raw() == receiver.raw(),
            },
        );
        ic_count_update();
        return Ok(());
    }

    let mut scratch = Vec::new();
    let new_entry =
        with_roots(vm, state, &mut scratch, |proxy, roots| unsafe {
            let old_values = (&*entries).elements();
            let new_len = old_values.len() + FEEDBACK_ENTRY_STRIDE;
            let size = size_of::<Array>() + new_len * size_of::<Value>();
            let layout = Layout::from_size_align(size, 8).unwrap();
            let ptr = proxy.allocate(layout, roots);

            let arr_ptr = ptr.as_ptr() as *mut Array;
            init_array(arr_ptr, new_len as u64);
            let elems_dst = arr_ptr.add(1) as *mut Value;
            ptr::copy_nonoverlapping(
                old_values.as_ptr(),
                elems_dst,
                old_values.len(),
            );
            ptr::copy_nonoverlapping(
                new_entry_values.as_ptr(),
                elems_dst.add(old_values.len()),
                FEEDBACK_ENTRY_STRIDE,
            );

            Value::from_ptr(arr_ptr)
        });
    array_set_entry(vm, feedback, feedback_idx as usize, new_entry);
    ic_count_update();

    Ok(())
}

pub(crate) fn dispatch_send(
    vm: &mut VM,
    state: &mut InterpreterState,
    frame_idx: usize,
    code_val: Value,
    message_idx: u16,
    reg: u16,
    argc: u8,
    feedback_idx: u16,
) -> Result<(), RuntimeError> {
    let receiver = state.acc;

    let code: &Code = unsafe { code_val.as_ref() };
    let message = unsafe { code.constant(message_idx as u32) };
    #[cfg(debug_assertions)]
    {
        if let Some(trace_name) = vm.trace_send_name.as_deref() {
            if let Some(name) = symbol_to_string(message) {
                if name == trace_name {
                    let pc = state.frames[frame_idx].pc;
                    let holder = state.frames[frame_idx].holder;
                    let holder_slot = state.frames[frame_idx].holder_slot_index;
                    let holder_name = holder_slot_name(holder, holder_slot);
                    eprintln!(
                        "trace_send {} pc={} holder={} recv={:?} {}",
                        name,
                        pc,
                        holder_name,
                        receiver,
                        debug_value_summary(receiver)
                    );
                }
            }
        }
    }
    let mut receiver_feedback_map = vm.special.none;
    let mut megamorphic_key = MegamorphicKey {
        message_raw: 0,
        receiver_map_raw: 0,
        holder_raw: 0,
        delegate_raw: 0,
    };
    if IC_CACHE_ENABLED {
        receiver_feedback_map = feedback_map_for_receiver(vm, receiver)?;
        megamorphic_key =
            megamorphic_key_for_send(message, receiver_feedback_map);
        if try_dispatch_feedback_entry(
            vm,
            state,
            frame_idx,
            code,
            feedback_idx,
            megamorphic_key,
            receiver,
            receiver_feedback_map,
            reg,
            argc,
        )? {
            return Ok(());
        }
        ic_count_miss();
    }

    let result = unsafe { object::lookup(receiver, message, &vm.special) };
    match result {
        object::LookupResult::None => {
            Err(RuntimeError::MessageNotUnderstood { receiver, message })
        }
        object::LookupResult::Found {
            holder,
            slot,
            slot_index,
            traversed_assignable_parent,
        } => {
            if IC_CACHE_ENABLED {
                update_send_feedback_entry(
                    vm,
                    state,
                    code,
                    feedback_idx,
                    megamorphic_key,
                    receiver,
                    receiver_feedback_map,
                    holder,
                    slot_index,
                    traversed_assignable_parent,
                )?;
            }
            dispatch_slot(
                vm, state, frame_idx, receiver, holder, slot, slot_index, reg,
                argc,
            )
        }
    }
}

pub(crate) fn call_block(
    vm: &mut VM,
    state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    if !is_block_value(receiver)? {
        return Err(RuntimeError::TypeError {
            expected: "block",
            got: receiver,
        });
    }
    let block_code = block_code(receiver, vm.special.none)?;
    let block_env = block_env(receiver, vm.special.none)?;
    let receiver_self = block_self(receiver)?;
    let current_idx = current_frame_index(state);
    let module_path =
        current_idx.and_then(|idx| state.frames[idx].module_path.clone());
    let module_dynamic = current_idx
        .map(|idx| state.frames[idx].module_dynamic)
        .unwrap_or(false);
    push_block_frame_with_args(
        vm,
        state,
        block_code,
        receiver_self,
        args,
        block_env,
        module_path,
        module_dynamic,
    )?;
    Ok(state.acc)
}

pub(crate) fn install_handler(state: &mut InterpreterState, handler: Value) {
    state.handlers.push(HandlerScope {
        scope_depth: state.frames.len(),
        handler,
    });
}

pub(crate) fn install_finalizer(state: &mut InterpreterState, cleanup: Value) {
    state.finalizers.push(FinalizerScope {
        scope_depth: state.frames.len(),
        cleanup,
    });
}

pub(crate) fn signal_condition(
    vm: &mut VM,
    state: &mut InterpreterState,
    condition: Value,
) -> Result<(), RuntimeError> {
    let frame_depth = state.frames.len();
    let Some(handler) = state
        .handlers
        .iter()
        .rev()
        .find(|scope| frame_depth > scope.scope_depth)
        .copied()
    else {
        return Err(RuntimeError::UnhandledSignal { condition });
    };
    call_block(vm, state, handler.handler, &[condition])?;
    Ok(())
}

pub(crate) fn request_unwind(
    state: &mut InterpreterState,
    value: Value,
) -> Result<(), RuntimeError> {
    let frame_depth = state.frames.len();
    let Some(handler) = state
        .handlers
        .iter()
        .rev()
        .find(|scope| frame_depth > scope.scope_depth)
        .copied()
    else {
        return Err(RuntimeError::UnwindWithoutHandler);
    };
    state.unwind = Some(UnwindState {
        target_depth: handler.scope_depth,
        value,
    });
    Ok(())
}

fn dispatch_resend(
    vm: &mut VM,
    state: &mut InterpreterState,
    frame_idx: usize,
    code_val: Value,
    message_idx: u16,
    reg: u16,
    argc: u8,
    feedback_idx: u16,
    delegate_idx: Option<u16>,
) -> Result<(), RuntimeError> {
    let receiver = get_register(state, frame_idx, 0)?;
    let holder = state.frames[frame_idx].holder;

    let code: &Code = unsafe { code_val.as_ref() };
    let message = unsafe { code.constant(message_idx as u32) };
    let delegate_name =
        delegate_idx.map(|idx| unsafe { code.constant(idx as u32) });

    let mut receiver_feedback_map = vm.special.none;
    let mut megamorphic_key = MegamorphicKey {
        message_raw: 0,
        receiver_map_raw: 0,
        holder_raw: 0,
        delegate_raw: 0,
    };
    if IC_CACHE_ENABLED {
        receiver_feedback_map = feedback_map_for_receiver(vm, receiver)?;
        megamorphic_key = megamorphic_key_for_resend(
            message,
            receiver_feedback_map,
            holder,
            delegate_name,
        );
        if try_dispatch_feedback_entry(
            vm,
            state,
            frame_idx,
            code,
            feedback_idx,
            megamorphic_key,
            receiver,
            receiver_feedback_map,
            reg,
            argc,
        )? {
            return Ok(());
        }
        ic_count_miss();
    }

    let result = lookup_resend(holder, message, delegate_name, &vm.special)?;
    match result {
        object::LookupResult::None => {
            Err(RuntimeError::MessageNotUnderstood { receiver, message })
        }
        object::LookupResult::Found {
            holder,
            slot,
            slot_index,
            traversed_assignable_parent,
        } => {
            if IC_CACHE_ENABLED {
                update_send_feedback_entry(
                    vm,
                    state,
                    code,
                    feedback_idx,
                    megamorphic_key,
                    receiver,
                    receiver_feedback_map,
                    holder,
                    slot_index,
                    traversed_assignable_parent,
                )?;
            }
            dispatch_slot(
                vm, state, frame_idx, receiver, holder, slot, slot_index, reg,
                argc,
            )
        }
    }
}

fn dispatch_slot(
    vm: &mut VM,
    state: &mut InterpreterState,
    frame_idx: usize,
    receiver: Value,
    holder: Value,
    slot: Slot,
    slot_index: u32,
    reg: u16,
    argc: u8,
) -> Result<(), RuntimeError> {
    if slot.is_assignment() {
        let value = get_register(state, frame_idx, reg)?;
        write_holder_value(vm, holder, slot.value, value)?;
        state.acc = value;
        return Ok(());
    }

    if slot.is_assignable() {
        state.acc = slot.value;
        return Ok(());
    }

    if let Some(target) = extract_method_target(slot.value, vm.special.none)? {
        match target {
            MethodTarget::Code {
                code: code_val,
                tail_call,
            } => {
                let method_module = state.frames[frame_idx].module_path.clone();
                if try_tail_recursive_self_call(
                    vm,
                    state,
                    frame_idx,
                    receiver,
                    holder,
                    slot_index,
                    code_val,
                    reg,
                    argc,
                    method_module.as_deref(),
                    false,
                    tail_call,
                )? {
                    return Ok(());
                }
                return push_method_frame(
                    vm,
                    state,
                    code_val,
                    receiver,
                    Some((frame_idx, reg, argc)),
                    holder,
                    slot_index,
                    method_module,
                    false,
                );
            }
            MethodTarget::Primitive(index) => {
                let primitive = vm.primitives.get(index).ok_or(
                    RuntimeError::TypeError {
                        expected: "primitive index",
                        got: Value::from_i64(index as i64),
                    },
                )?;
                if primitive.arity != argc {
                    return Err(RuntimeError::TypeError {
                        expected: "argument count",
                        got: Value::from_i64(argc as i64),
                    });
                }
                let start = reg as usize;
                let end = start + argc as usize;
                let (reg_base, reg_len) = {
                    let frame = &state.frames[frame_idx];
                    (frame.reg_base, frame.reg_len)
                };
                if end > reg_len {
                    return Err(RuntimeError::TypeError {
                        expected: "argument register range",
                        got: Value::from_i64(end as i64),
                    });
                }
                let args = unsafe {
                    let ptr =
                        state.register_stack.as_ptr().add(reg_base + start);
                    core::slice::from_raw_parts(ptr, argc as usize)
                };
                state.acc = (primitive.func)(vm, state, receiver, args)?;
                return Ok(());
            }
        }
    }

    state.acc = slot.value;
    Ok(())
}

fn next_instruction_is_local_return(
    state: &InterpreterState,
    frame_idx: usize,
) -> bool {
    let frame = &state.frames[frame_idx];
    if !frame.code.is_ref() {
        return false;
    }
    let code: &Code = unsafe { frame.code.as_ref() };
    let bytecode = unsafe { code.bytecode() };
    if frame.pc >= bytecode.len() {
        return false;
    }
    let (instr, _) = decode_at(bytecode, frame.pc);
    matches!(instr, Instruction::LocalReturn)
}

fn try_tail_recursive_self_call(
    vm: &mut VM,
    state: &mut InterpreterState,
    frame_idx: usize,
    receiver: Value,
    holder: Value,
    holder_slot_index: u32,
    code_val: Value,
    reg: u16,
    argc: u8,
    module_path: Option<&str>,
    module_dynamic: bool,
    tail_call: bool,
) -> Result<bool, RuntimeError> {
    if !tail_call {
        return Ok(false);
    }
    let mut method_idx = None;
    for idx in (0..=frame_idx).rev() {
        let frame = &state.frames[idx];
        if frame.is_block {
            continue;
        }
        if frame.code.raw() != code_val.raw() {
            continue;
        }
        if frame.holder.raw() != holder.raw()
            || frame.holder_slot_index != holder_slot_index
        {
            continue;
        }
        if unsafe { read_register_unchecked(state, frame.reg_base, 0) }.raw()
            != receiver.raw()
        {
            continue;
        }
        method_idx = Some(idx);
        break;
    }
    let Some(method_idx) = method_idx else {
        return Ok(false);
    };
    for idx in method_idx..=frame_idx {
        if !next_instruction_is_local_return(state, idx) {
            return Ok(false);
        }
    }

    let code = unsafe { &*expect_code(code_val)? };
    let arg_count = code.arg_count() as usize;
    let provided = argc as usize;
    if provided != arg_count {
        return Err(RuntimeError::TypeError {
            expected: "argument count",
            got: Value::from_i64(provided as i64),
        });
    }

    let none = vm.special.none;
    let new_temp_array = if code.temp_count() > 0 {
        state.acc = receiver;
        alloc_temp_array(vm, state, code.temp_count(), none)?
    } else {
        none
    };
    let receiver = state.acc;

    let reg_count = code.register_count() as usize;
    let method_reg_base = state.frames[method_idx].reg_base;
    let method_reg_len = state.frames[method_idx].reg_len;
    debug_assert_eq!(method_reg_len, reg_count.max(1));
    let src_reg_len = state.frames[frame_idx].reg_len;
    let start = reg as usize;
    let end = start + argc as usize;
    if end > src_reg_len || argc as usize + 1 > method_reg_len {
        return Err(RuntimeError::TypeError {
            expected: "argument register range",
            got: Value::from_i64(end as i64),
        });
    }
    let src_base = state.frames[frame_idx].reg_base + start;
    unsafe {
        let src = state.register_stack.as_ptr().add(src_base);
        let dst = state.register_stack.as_mut_ptr().add(method_reg_base + 1);
        core::ptr::copy(src, dst, argc as usize);
        write_register_unchecked(state, method_reg_base, 0, receiver);
    }
    let clear_start = method_reg_base + 1 + argc as usize;
    let clear_end = method_reg_base + method_reg_len;
    if clear_start < clear_end {
        state.register_stack[clear_start..clear_end].fill(none);
    }

    if frame_idx > method_idx {
        truncate_frames(state, method_idx + 1);
    }

    let frame = &mut state.frames[method_idx];
    frame.code = code_val;
    frame.pc = 0;
    frame.temp_array = new_temp_array;
    frame.method_frame_idx = method_idx;
    frame.holder = holder;
    frame.holder_slot_index = holder_slot_index;
    frame.module_path = module_path.map(str::to_owned);
    frame.module_dynamic = module_dynamic;

    Ok(true)
}

fn create_object(
    vm: &mut VM,
    state: &mut InterpreterState,
    frame_idx: usize,
    code_val: Value,
    map_idx: u16,
    values_reg: u16,
) -> Result<Value, RuntimeError> {
    let code: &Code = unsafe { code_val.as_ref() };
    let map_val = unsafe { code.constant(map_idx as u32) };
    let map = unsafe { &*expect_map(map_val)? };
    let value_count = map.value_count() as usize;

    let values_start = values_reg as usize;
    let values_end = values_start + value_count;
    if value_count > 0 {
        let reg_len = state.frames[frame_idx].reg_len;
        if values_end > reg_len {
            return Err(RuntimeError::TypeError {
                expected: "register range",
                got: Value::from_i64(values_end as i64),
            });
        }
    }

    let mut scratch = vec![map_val];
    let obj = with_roots(vm, state, &mut scratch, |proxy, roots| {
        let size = slot_object_allocation_size(value_count as u32);
        let layout = Layout::from_size_align(size, 8).unwrap();
        let ptr = proxy.allocate(layout, roots);
        let map_val = roots.scratch[0];
        let obj_ptr = ptr.as_ptr() as *mut SlotObject;
        unsafe {
            ptr::write(
                obj_ptr,
                SlotObject {
                    header: Header::new(ObjectType::Slots),
                    map: map_val,
                },
            );

            if value_count > 0 {
                let vals_dst = obj_ptr.add(1) as *mut Value;
                for i in 0..value_count {
                    *vals_dst.add(i) =
                        read_register(roots.state, frame_idx, values_start + i);
                }
            }

            Value::from_ptr(obj_ptr)
        }
    });

    Ok(obj)
}

fn create_block(
    vm: &mut VM,
    state: &mut InterpreterState,
    code_val: Value,
    block_idx: u16,
) -> Result<Value, RuntimeError> {
    let code: &Code = unsafe { code_val.as_ref() };
    let map_val = unsafe { code.constant(block_idx as u32) };
    let _map = unsafe { &*expect_map(map_val)? };
    let (env, self_value) = state
        .frames
        .last()
        .map(|f| (f.temp_array, read_register_at(state, f.reg_base, 0)))
        .unwrap_or((vm.special.none, vm.special.none));
    let mut scratch = vec![map_val, env, self_value];
    let block = with_roots(vm, state, &mut scratch, |proxy, roots| {
        let size = size_of::<Block>();
        let layout = Layout::from_size_align(size, 8).unwrap();
        let ptr = proxy.allocate(layout, roots);
        let map_val = roots.scratch[0];
        let env_val = roots.scratch[1];
        let self_val = roots.scratch[2];
        let block_ptr = ptr.as_ptr() as *mut Block;
        unsafe {
            ptr::write(
                block_ptr,
                Block {
                    header: Header::new(ObjectType::Block),
                    map: map_val,
                    env: env_val,
                    self_value: self_val,
                },
            );
            Value::from_ptr(block_ptr)
        }
    });

    Ok(block)
}

fn alloc_temp_array(
    vm: &mut VM,
    state: &mut InterpreterState,
    len: u16,
    parent: Value,
) -> Result<Value, RuntimeError> {
    let mut scratch = Vec::new();
    let arr = with_roots(vm, state, &mut scratch, |proxy, roots| {
        let size = size_of::<Array>() + (len as usize + 1) * size_of::<Value>();
        let layout = Layout::from_size_align(size, 8).unwrap();
        let ptr = proxy.allocate(layout, roots);
        let arr_ptr = ptr.as_ptr() as *mut Array;
        unsafe {
            init_array(arr_ptr, len as u64 + 1);
            let none = roots.special.none;
            let elems = arr_ptr.add(1) as *mut Value;
            *elems = parent;
            for i in 0..len as usize {
                *elems.add(i + 1) = none;
            }
        }
        Value::from_ptr(arr_ptr)
    });

    Ok(arr)
}

fn load_assoc(
    vm: &VM,
    code_val: Value,
    idx: u16,
) -> Result<Value, RuntimeError> {
    let code: &Code = unsafe { code_val.as_ref() };
    let cell = unsafe { code.constant(idx as u32) };
    let assoc_obj = unsafe { &*expect_slot_object(cell)? };
    if assoc_obj.map.raw() != vm.assoc_map.raw() {
        return Err(RuntimeError::TypeError {
            expected: "global cell",
            got: cell,
        });
    }
    let value = unsafe { assoc_obj.read_value(SlotObject::VALUES_OFFSET) };
    Ok(value)
}

fn store_assoc(
    vm: &mut VM,
    code_val: Value,
    idx: u16,
    value: Value,
) -> Result<(), RuntimeError> {
    let code: &Code = unsafe { code_val.as_ref() };
    let cell = unsafe { code.constant(idx as u32) };
    let assoc_obj = unsafe { &mut *expect_slot_object_mut(cell)? };
    if assoc_obj.map.raw() != vm.assoc_map.raw() {
        return Err(RuntimeError::TypeError {
            expected: "global cell",
            got: cell,
        });
    }
    unsafe { assoc_obj.write_value(SlotObject::VALUES_OFFSET, value) };
    if value.is_ref() {
        vm.heap_proxy.write_barrier(cell, value);
    }
    Ok(())
}

fn symbol_to_string(sym: Value) -> Option<String> {
    if !sym.is_ref() {
        return None;
    }

    let header: &Header = unsafe { sym.as_ref() };
    if header.object_type() != ObjectType::Symbol {
        return None;
    }

    let s: &VMSymbol = unsafe { sym.as_ref() };
    Some(unsafe { s.as_str() }.to_string())
}

#[cfg(debug_assertions)]
fn holder_slot_name(holder: Value, slot_index: u32) -> String {
    if !holder.is_ref() {
        return "<none>".to_string();
    }
    let header: &Header = unsafe { holder.as_ref() };
    if header.object_type() != ObjectType::Slots {
        return format!("{:?}", header.object_type());
    }
    let holder_obj: &SlotObject = unsafe { holder.as_ref() };
    let map: &Map = unsafe { holder_obj.map.as_ref() };
    unsafe {
        let slots = map.slots();
        let idx = slot_index as usize;
        if idx >= slots.len() {
            return "<unknown>".to_string();
        }
        let name = slots[idx].name;
        symbol_to_string(name).unwrap_or_else(|| "<symbol>".to_string())
    }
}

#[cfg(debug_assertions)]
fn debug_value_summary(value: Value) -> String {
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
            let map: &Map = obj.map.as_ref();
            format!(
                "slots map_slots={} value_count={}",
                map.slot_count(),
                map.value_count()
            )
        },
        ObjectType::Map => unsafe {
            let map: &Map = value.as_ref();
            format!(
                "map slots={} value_count={}",
                map.slot_count(),
                map.value_count()
            )
        },
        ObjectType::Str => "string".to_string(),
        ObjectType::Symbol => "symbol".to_string(),
        ObjectType::Array => "array".to_string(),
        ObjectType::ByteArray => "bytearray".to_string(),
        ObjectType::Float => "float".to_string(),
        ObjectType::Ratio => "ratio".to_string(),
        ObjectType::BigNum => "bignum".to_string(),
        _ => format!("{:?}", header.object_type()),
    }
}

fn load_temp(
    vm: &VM,
    state: &InterpreterState,
    frame_idx: usize,
    array_idx: u16,
    idx: u16,
) -> Result<Value, RuntimeError> {
    let array =
        get_temp_array(&state.frames[frame_idx], array_idx, vm.special.none)?;
    let array = unsafe { &*expect_array(array)? };
    let value_idx = idx as u64 + 1;
    if value_idx >= array.len() {
        return Err(RuntimeError::TypeError {
            expected: "temp index",
            got: Value::from_i64(idx as i64),
        });
    }
    unsafe {
        let elems = (array as *const Array).add(1) as *const Value;
        Ok(*elems.add(value_idx as usize))
    }
}

fn store_temp(
    vm: &mut VM,
    state: &mut InterpreterState,
    frame_idx: usize,
    array_idx: u16,
    idx: u16,
    value: Value,
) -> Result<(), RuntimeError> {
    let array_val =
        get_temp_array(&state.frames[frame_idx], array_idx, vm.special.none)?;
    let array = unsafe { &*expect_array(array_val)? };
    let value_idx = idx as u64 + 1;
    if value_idx >= array.len() {
        return Err(RuntimeError::TypeError {
            expected: "temp index",
            got: Value::from_i64(idx as i64),
        });
    }
    unsafe {
        let elems = (array as *const Array).add(1) as *mut Value;
        *elems.add(value_idx as usize) = value;
    }
    if value.is_ref() {
        vm.heap_proxy.write_barrier(array_val, value);
    }
    Ok(())
}

fn get_temp_array(
    frame: &Frame,
    array_idx: u16,
    none: Value,
) -> Result<Value, RuntimeError> {
    if frame.temp_array.raw() == none.raw() {
        return Err(RuntimeError::TypeError {
            expected: "temp array",
            got: frame.temp_array,
        });
    }
    let mut array = frame.temp_array;
    let mut depth = array_idx;
    while depth > 0 {
        array = temp_array_parent(array, none)?;
        depth -= 1;
    }
    Ok(array)
}

fn temp_array_parent(
    array_val: Value,
    none: Value,
) -> Result<Value, RuntimeError> {
    let array = unsafe { &*expect_array(array_val)? };
    if array.len() == 0 {
        return Err(RuntimeError::TypeError {
            expected: "temp array parent",
            got: array_val,
        });
    }
    unsafe {
        let elems = (array as *const Array).add(1) as *const Value;
        let parent = *elems;
        if parent.raw() == none.raw() {
            return Err(RuntimeError::TypeError {
                expected: "temp array parent",
                got: parent,
            });
        }
        Ok(parent)
    }
}

fn copy_args_from_frame(
    state: &mut InterpreterState,
    frame_idx: usize,
    reg: u16,
    argc: u8,
    out_reg_base: usize,
    out_reg_len: usize,
) -> Result<(), RuntimeError> {
    if argc == 0 {
        return Ok(());
    }

    let start = reg as usize;
    let end = start + argc as usize;
    let (in_reg_base, in_reg_len) = {
        let frame = &state.frames[frame_idx];
        (frame.reg_base, frame.reg_len)
    };
    if end > in_reg_len {
        return Err(RuntimeError::TypeError {
            expected: "argument register range",
            got: Value::from_i64(end as i64),
        });
    }
    if 1 + argc as usize > out_reg_len {
        return Err(RuntimeError::TypeError {
            expected: "argument register range",
            got: Value::from_i64((1 + argc as usize) as i64),
        });
    }
    unsafe {
        let src = state.register_stack.as_ptr().add(in_reg_base + start);
        let dst = state.register_stack.as_mut_ptr().add(out_reg_base + 1);
        core::ptr::copy(src, dst, argc as usize);
    }
    Ok(())
}

enum MethodTarget {
    Code { code: Value, tail_call: bool },
    Primitive(usize),
}

fn extract_method_target(
    value: Value,
    none: Value,
) -> Result<Option<MethodTarget>, RuntimeError> {
    if !value.is_ref() {
        return Ok(None);
    }
    let header: &Header = unsafe { value.as_ref() };
    match header.object_type() {
        ObjectType::Code => Ok(Some(MethodTarget::Code {
            code: value,
            tail_call: false,
        })),
        ObjectType::Slots => {
            let obj: &SlotObject = unsafe { value.as_ref() };
            let map: &Map = unsafe { obj.map.as_ref() };
            if !map.has_code() {
                return Ok(None);
            }
            if map.is_primitive() {
                let code = map.code;
                if !code.is_fixnum() {
                    return Err(RuntimeError::TypeError {
                        expected: "primitive index",
                        got: code,
                    });
                }
                let idx = unsafe { code.to_i64() };
                if idx < 0 {
                    return Err(RuntimeError::TypeError {
                        expected: "primitive index",
                        got: code,
                    });
                }
                Ok(Some(MethodTarget::Primitive(idx as usize)))
            } else {
                if map.code.raw() == none.raw() {
                    return Err(RuntimeError::TypeError {
                        expected: "method code",
                        got: map.code,
                    });
                }
                Ok(Some(MethodTarget::Code {
                    code: map.code,
                    tail_call: map.is_tail_call(),
                }))
            }
        }
        _ => Ok(None),
    }
}

fn is_block_value(value: Value) -> Result<bool, RuntimeError> {
    if !value.is_ref() {
        return Ok(false);
    }
    let header: &Header = unsafe { value.as_ref() };
    Ok(header.object_type() == ObjectType::Block)
}

fn block_code(block_val: Value, none: Value) -> Result<Value, RuntimeError> {
    let block = unsafe { &*expect_block(block_val)? };
    let map: &Map = unsafe { block.map.as_ref() };
    if map.code.raw() == none.raw() {
        return Err(RuntimeError::TypeError {
            expected: "block code",
            got: map.code,
        });
    }
    Ok(map.code)
}

fn block_env(block_val: Value, none: Value) -> Result<Value, RuntimeError> {
    let block = unsafe { &*expect_block(block_val)? };
    let env = block.env;
    if env.raw() == none.raw() {
        return Ok(none);
    }
    Ok(env)
}

fn block_self(block_val: Value) -> Result<Value, RuntimeError> {
    let block = unsafe { &*expect_block(block_val)? };
    Ok(block.self_value)
}

fn lookup_resend(
    holder: Value,
    message: Value,
    delegate_name: Option<Value>,
    specials: &object::SpecialObjects,
) -> Result<object::LookupResult, RuntimeError> {
    if !holder.is_ref() {
        return Ok(object::LookupResult::None);
    }

    let map_val = holder_map(holder)?;
    let map = unsafe { &*(map_val.ref_bits() as *const Map) };
    let slots = unsafe { map.slots() };

    for slot in slots.iter() {
        if !slot.is_parent() {
            continue;
        }
        if let Some(delegate) = delegate_name {
            if slot.name.raw() != delegate.raw() {
                continue;
            }
        }

        let parent = read_parent_value(holder, slot)?;
        let result = unsafe { object::lookup(parent, message, specials) };
        if !matches!(result, object::LookupResult::None) {
            return Ok(result);
        }
    }

    Ok(object::LookupResult::None)
}

fn holder_map(holder: Value) -> Result<Value, RuntimeError> {
    let header: &Header = unsafe { holder.as_ref() };
    match header.object_type() {
        ObjectType::Slots => {
            let obj: &SlotObject = unsafe { holder.as_ref() };
            Ok(obj.map)
        }
        ObjectType::Block => {
            let obj: &Block = unsafe { holder.as_ref() };
            Ok(obj.map)
        }
        ObjectType::Map => {
            let map: &Map = unsafe { holder.as_ref() };
            Ok(map.map)
        }
        _ => Err(RuntimeError::TypeError {
            expected: "holder map",
            got: holder,
        }),
    }
}

fn read_parent_value(
    holder: Value,
    slot: &Slot,
) -> Result<Value, RuntimeError> {
    if slot.is_assignable() {
        let offset = unsafe { slot.value.to_i64() } as u32;
        read_holder_value(holder, offset)
    } else {
        Ok(slot.value)
    }
}

fn read_holder_value(
    holder: Value,
    offset: u32,
) -> Result<Value, RuntimeError> {
    let header: &Header = unsafe { holder.as_ref() };
    match header.object_type() {
        ObjectType::Slots | ObjectType::Block => {
            let obj: &SlotObject = unsafe { holder.as_ref() };
            unsafe { Ok(obj.read_value(offset)) }
        }
        ObjectType::Map => {
            let ptr = holder.ref_bits() as *const u8;
            unsafe { Ok(*(ptr.add(offset as usize) as *const Value)) }
        }
        _ => Err(RuntimeError::TypeError {
            expected: "holder value",
            got: holder,
        }),
    }
}

fn write_holder_value(
    vm: &mut VM,
    holder: Value,
    offset_val: Value,
    value: Value,
) -> Result<(), RuntimeError> {
    let offset = unsafe { offset_val.to_i64() } as u32;
    let header: &Header = unsafe { holder.as_ref() };
    match header.object_type() {
        ObjectType::Slots | ObjectType::Block => {
            let obj = unsafe { &mut *expect_slot_object_mut(holder)? };
            unsafe { obj.write_value(offset, value) };
        }
        ObjectType::Map => {
            let ptr = holder.ref_bits() as *mut u8;
            unsafe { *(ptr.add(offset as usize) as *mut Value) = value };
        }
        _ => {
            return Err(RuntimeError::TypeError {
                expected: "holder value",
                got: holder,
            });
        }
    }
    if value.is_ref() {
        vm.heap_proxy.write_barrier(holder, value);
    }
    Ok(())
}

fn current_frame_index(state: &InterpreterState) -> Option<usize> {
    if state.frames.is_empty() {
        None
    } else {
        Some(state.frames.len() - 1)
    }
}

fn is_truthy(vm: &VM, value: Value) -> bool {
    let none = vm.special.none.raw();
    let false_obj = vm.special.false_obj.raw();
    let raw = value.raw();
    raw != none && raw != false_obj
}

fn alloc_frame_registers(
    state: &mut InterpreterState,
    reg_count: usize,
    none: Value,
) -> (usize, usize) {
    let reg_len = reg_count.max(1);
    let reg_base = state.register_top;
    let new_top = reg_base + reg_len;
    state.register_stack.reserve(reg_len);
    if new_top > state.register_stack.len() {
        state.register_stack.resize(new_top, none);
    }
    unsafe { fill_registers_unchecked(state, reg_base, reg_len, none) };
    state.register_top = new_top;
    (reg_base, reg_len)
}

fn truncate_frames(state: &mut InterpreterState, len: usize) {
    state.frames.truncate(len);
    state.register_top = state
        .frames
        .last()
        .map(|f| f.reg_base + f.reg_len)
        .unwrap_or(0);
    prune_handlers(state, len);
}

fn pop_frame(state: &mut InterpreterState) {
    if state.frames.pop().is_some() {
        state.register_top = state
            .frames
            .last()
            .map(|f| f.reg_base + f.reg_len)
            .unwrap_or(0);
        prune_handlers(state, state.frames.len());
    }
}

#[inline(always)]
fn prune_handlers(state: &mut InterpreterState, frame_depth: usize) {
    while state
        .handlers
        .last()
        .is_some_and(|scope| scope.scope_depth >= frame_depth)
    {
        state.handlers.pop();
    }
}

#[inline(always)]
unsafe fn read_register_unchecked(
    state: &InterpreterState,
    reg_base: usize,
    reg: usize,
) -> Value {
    state.register_stack[reg_base + reg]
}

#[inline(always)]
unsafe fn write_register_unchecked(
    state: &mut InterpreterState,
    reg_base: usize,
    reg: usize,
    value: Value,
) {
    state.register_stack[reg_base + reg] = value;
}

#[inline(always)]
unsafe fn fill_registers_unchecked(
    state: &mut InterpreterState,
    reg_base: usize,
    reg_len: usize,
    value: Value,
) {
    state.register_stack[reg_base..reg_base + reg_len].fill(value);
}

#[inline(always)]
fn read_register_at(
    state: &InterpreterState,
    reg_base: usize,
    reg: usize,
) -> Value {
    unsafe { read_register_unchecked(state, reg_base, reg) }
}

#[inline(always)]
fn read_register(
    state: &InterpreterState,
    frame_idx: usize,
    reg: usize,
) -> Value {
    let frame = &state.frames[frame_idx];
    debug_assert!(reg < frame.reg_len);
    unsafe { read_register_unchecked(state, frame.reg_base, reg) }
}

#[inline(always)]
fn get_register(
    state: &InterpreterState,
    frame_idx: usize,
    reg: u16,
) -> Result<Value, RuntimeError> {
    let frame = &state.frames[frame_idx];
    let idx = reg as usize;
    if idx >= frame.reg_len {
        return Err(RuntimeError::TypeError {
            expected: "register",
            got: Value::from_i64(reg as i64),
        });
    }
    Ok(unsafe { read_register_unchecked(state, frame.reg_base, idx) })
}

#[inline(always)]
fn set_register(
    state: &mut InterpreterState,
    frame_idx: usize,
    reg: u16,
    value: Value,
) -> Result<(), RuntimeError> {
    let (reg_base, reg_len) = {
        let frame = &state.frames[frame_idx];
        (frame.reg_base, frame.reg_len)
    };
    let idx = reg as usize;
    if idx >= reg_len {
        return Err(RuntimeError::TypeError {
            expected: "register",
            got: Value::from_i64(reg as i64),
        });
    }
    unsafe { write_register_unchecked(state, reg_base, idx, value) };
    Ok(())
}

fn ensure_frame_register_len(
    state: &mut InterpreterState,
    frame_idx: usize,
    required_len: usize,
    none: Value,
) {
    let (reg_base, reg_len) = {
        let frame = &state.frames[frame_idx];
        (frame.reg_base, frame.reg_len)
    };
    if required_len <= reg_len {
        return;
    }
    debug_assert_eq!(frame_idx + 1, state.frames.len());
    debug_assert_eq!(reg_base + reg_len, state.register_top);

    let grow_by = required_len - reg_len;
    let new_top = state.register_top + grow_by;
    state.register_stack.reserve(grow_by);
    if new_top > state.register_stack.len() {
        state.register_stack.resize(new_top, none);
    }
    unsafe {
        fill_registers_unchecked(state, reg_base + reg_len, grow_by, none)
    };
    state.register_top = new_top;
    state.frames[frame_idx].reg_len = required_len;
}

fn load_stack_slot(
    state: &mut InterpreterState,
    frame_idx: usize,
    offset: u32,
    none: Value,
) -> Value {
    let idx = offset as usize;
    ensure_frame_register_len(state, frame_idx, idx + 1, none);
    let base = state.frames[frame_idx].reg_base;
    unsafe { read_register_unchecked(state, base, idx) }
}

fn store_stack_slot(
    state: &mut InterpreterState,
    frame_idx: usize,
    offset: u32,
    value: Value,
    none: Value,
) {
    let idx = offset as usize;
    ensure_frame_register_len(state, frame_idx, idx + 1, none);
    let base = state.frames[frame_idx].reg_base;
    unsafe { write_register_unchecked(state, base, idx, value) };
}

fn jump_target(pc: usize, offset: i16) -> Result<usize, RuntimeError> {
    let next = (pc as isize).checked_add(offset as isize).ok_or(
        RuntimeError::TypeError {
            expected: "jump target",
            got: Value::from_i64(offset as i64),
        },
    )?;
    if next < 0 {
        return Err(RuntimeError::TypeError {
            expected: "jump target",
            got: Value::from_i64(offset as i64),
        });
    }
    Ok(next as usize)
}

fn expect_code(value: Value) -> Result<*const Code, RuntimeError> {
    if !value.is_ref() {
        return Err(RuntimeError::TypeError {
            expected: "code",
            got: value,
        });
    }
    let header: &Header = unsafe { value.as_ref() };
    if header.object_type() != ObjectType::Code {
        return Err(RuntimeError::TypeError {
            expected: "code",
            got: value,
        });
    }
    Ok(value.ref_bits() as *const Code)
}

fn expect_map(value: Value) -> Result<*const Map, RuntimeError> {
    if !value.is_ref() {
        return Err(RuntimeError::TypeError {
            expected: "map",
            got: value,
        });
    }
    let header: &Header = unsafe { value.as_ref() };
    if header.object_type() != ObjectType::Map {
        return Err(RuntimeError::TypeError {
            expected: "map",
            got: value,
        });
    }
    Ok(value.ref_bits() as *const Map)
}

fn expect_block(value: Value) -> Result<*const Block, RuntimeError> {
    if !value.is_ref() {
        return Err(RuntimeError::TypeError {
            expected: "block",
            got: value,
        });
    }
    let header: &Header = unsafe { value.as_ref() };
    if header.object_type() != ObjectType::Block {
        return Err(RuntimeError::TypeError {
            expected: "block",
            got: value,
        });
    }
    Ok(value.ref_bits() as *const Block)
}

fn expect_slot_object(value: Value) -> Result<*const SlotObject, RuntimeError> {
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

fn expect_slot_object_mut(
    value: Value,
) -> Result<*mut SlotObject, RuntimeError> {
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
    Ok(value.ref_bits() as *mut SlotObject)
}

fn expect_array(value: Value) -> Result<*const Array, RuntimeError> {
    if !value.is_ref() {
        return Err(RuntimeError::TypeError {
            expected: "array",
            got: value,
        });
    }
    let header: &Header = unsafe { value.as_ref() };
    if header.object_type() != ObjectType::Array {
        return Err(RuntimeError::TypeError {
            expected: "array",
            got: value,
        });
    }
    Ok(value.ref_bits() as *const Array)
}

pub(crate) fn with_roots<T>(
    vm: &mut VM,
    state: &mut InterpreterState,
    scratch: &mut Vec<Value>,
    f: impl FnOnce(&mut HeapProxy, &mut InterpreterRoots<'_>) -> T,
) -> T {
    let (proxy, special, assoc_map, dictionary) = (
        &mut vm.heap_proxy,
        &mut vm.special,
        &mut vm.assoc_map,
        &mut vm.dictionary,
    );
    let mut intern_table = vm
        .shared
        .intern_table
        .lock()
        .expect("intern table poisoned");
    let mut modules = vm.shared.modules.lock().expect("modules poisoned");
    let mut roots = InterpreterRoots {
        state,
        special,
        intern_table: &mut intern_table,
        assoc_map,
        dictionary,
        modules: &mut modules,
        scratch,
    };
    f(proxy, &mut roots)
}

pub(crate) fn primitive_extend_with(
    vm: &mut VM,
    state: &mut InterpreterState,
    target: Value,
    source: Value,
) -> Result<Value, RuntimeError> {
    let target_ptr = expect_slot_object_mut(target)?;
    let source_ptr = expect_slot_object(source)?;

    let source_obj = unsafe { &*source_ptr };
    let source_map_val = source_obj.map;
    let source_map: &Map = unsafe { source_map_val.as_ref() };
    if source_map.has_code() {
        return Err(RuntimeError::Unimplemented {
            message: "extend: source has code",
        });
    }
    let mut append_slots: Vec<(u32, bool)> = Vec::new();
    let mut idx: u32 = 0;
    for slot in unsafe { source_map.slots() } {
        if slot.is_assignment() {
            return Err(RuntimeError::Unimplemented {
                message: "extend: assignable slot",
            });
        }
        if slot.is_constant() {
            append_slots.push((idx, false));
        } else if slot.is_assignable() {
            append_slots.push((idx, true));
        } else {
            return Err(RuntimeError::Unimplemented {
                message: "extend: unsupported slot kind",
            });
        }
        idx += 1;
    }

    let mut scratch = vec![target, source, source_map_val];
    let new_map = with_roots(vm, state, &mut scratch, |proxy, roots| unsafe {
        let map_map = roots.special.map_map;
        let target_val = roots.scratch[0];
        let source_val = roots.scratch[1];
        let source_map_val = roots.scratch[2];
        let target_obj = &*(target_val.ref_bits() as *mut SlotObject);
        let old_map_val = target_obj.map;
        let old_map: &Map = old_map_val.as_ref();
        let old_slot_count = old_map.slot_count();

        let new_slot_count = old_slot_count + append_slots.len() as u32;
        let size = map_allocation_size(new_slot_count);
        let layout = Layout::from_size_align(size, 8).unwrap();
        let ptr = proxy.allocate(layout, roots);
        let map_ptr = ptr.as_ptr() as *mut Map;
        let target_obj = &*(target_val.ref_bits() as *mut SlotObject);
        let old_map_val = target_obj.map;
        let old_map: &Map = old_map_val.as_ref();
        let old_code = old_map.code;
        let old_flags = old_map.flags();
        let old_value_count = old_map.value_count();
        init_map(
            map_ptr,
            map_map,
            old_code,
            old_flags,
            new_slot_count,
            old_value_count,
        );

        if new_slot_count > 0 {
            let slots_dst = map_ptr.add(1) as *mut Slot;
            if old_slot_count > 0 {
                let old_slots = old_map.slots();
                ptr::copy_nonoverlapping(
                    old_slots.as_ptr(),
                    slots_dst,
                    old_slot_count as usize,
                );
            }

            let source_map: &Map = source_map_val.as_ref();
            let source_obj = &*(source_val.ref_bits() as *const SlotObject);
            let mut out = slots_dst.add(old_slot_count as usize);
            for (slot_idx, was_assignable) in &append_slots {
                let slot = source_map.slot(*slot_idx);
                if *was_assignable {
                    let offset = slot.value.to_i64() as u32;
                    let value = source_obj.read_value(offset);
                    let flags = slot
                        .flags()
                        .without(SlotFlags::ASSIGNABLE)
                        .without(SlotFlags::ASSIGNMENT)
                        .with(SlotFlags::CONSTANT);
                    out.write(Slot::new(flags, slot.name, value));
                } else {
                    out.write(*slot);
                }
                out = out.add(1);
            }
        }

        Value::from_ptr(map_ptr)
    });

    let target_obj = unsafe { &mut *target_ptr };
    target_obj.map = new_map;
    vm.heap_proxy.write_barrier(target, new_map);
    Ok(target)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Width {
    Normal,
    Wide,
    ExtraWide,
}

fn decode_at(bytecode: &[u8], pc: usize) -> (Instruction, usize) {
    let mut pos = pc;
    let op_byte = read_u8(bytecode, &mut pos);
    let mut width = Width::Normal;
    let op = unsafe { Op::from_u8_unchecked(op_byte) };
    let op = match op {
        Op::Wide => {
            width = Width::Wide;
            let next = read_u8(bytecode, &mut pos);
            unsafe { Op::from_u8_unchecked(next) }
        }
        Op::ExtraWide => {
            width = Width::ExtraWide;
            let next = read_u8(bytecode, &mut pos);
            unsafe { Op::from_u8_unchecked(next) }
        }
        _ => op,
    };

    let wide = matches!(width, Width::Wide | Width::ExtraWide);
    let instr = match op {
        Op::LoadConstant => Instruction::LoadConstant {
            idx: read_u16(bytecode, &mut pos),
        },
        Op::LoadSmi => {
            let value = match width {
                Width::Normal => read_u8(bytecode, &mut pos) as i8 as i32,
                Width::Wide => read_i16(bytecode, &mut pos) as i32,
                Width::ExtraWide => read_i32(bytecode, &mut pos),
            };
            Instruction::LoadSmi { value }
        }
        Op::Return => Instruction::Return,
        Op::LocalReturn => Instruction::LocalReturn,
        Op::CreateObject => {
            let map_idx = read_u16(bytecode, &mut pos);
            let values_reg = read_reg(bytecode, &mut pos, wide);
            Instruction::CreateObject {
                map_idx,
                values_reg,
            }
        }
        Op::CreateBlock => {
            let block_idx = read_u16(bytecode, &mut pos);
            Instruction::CreateBlock { block_idx }
        }
        Op::Send => {
            let message_idx = read_u16(bytecode, &mut pos);
            let reg = read_reg(bytecode, &mut pos, wide);
            let argc = read_u8(bytecode, &mut pos);
            let feedback_idx = read_u16(bytecode, &mut pos);
            Instruction::Send {
                message_idx,
                reg,
                argc,
                feedback_idx,
            }
        }
        Op::LoadLocal => Instruction::LoadLocal {
            reg: read_reg(bytecode, &mut pos, wide),
        },
        Op::StoreLocal => Instruction::StoreLocal {
            reg: read_reg(bytecode, &mut pos, wide),
        },
        Op::LoadStack => Instruction::LoadStack {
            offset: read_u32(bytecode, &mut pos),
        },
        Op::StoreStack => Instruction::StoreStack {
            offset: read_u32(bytecode, &mut pos),
        },
        Op::LoadTemp => {
            let array_idx = read_u16(bytecode, &mut pos);
            let idx = read_u16(bytecode, &mut pos);
            Instruction::LoadTemp { array_idx, idx }
        }
        Op::StoreTemp => {
            let array_idx = read_u16(bytecode, &mut pos);
            let idx = read_u16(bytecode, &mut pos);
            Instruction::StoreTemp { array_idx, idx }
        }
        Op::LoadAssoc => Instruction::LoadAssoc {
            idx: read_u16(bytecode, &mut pos),
        },
        Op::StoreAssoc => Instruction::StoreAssoc {
            idx: read_u16(bytecode, &mut pos),
        },
        Op::Mov => {
            let dst = read_reg(bytecode, &mut pos, wide);
            let src = read_reg(bytecode, &mut pos, wide);
            Instruction::Mov { dst, src }
        }
        Op::MovToStack => {
            let offset = read_u32(bytecode, &mut pos);
            let src = read_reg(bytecode, &mut pos, wide);
            Instruction::MovToStack { offset, src }
        }
        Op::MovFromStack => {
            let dst = read_reg(bytecode, &mut pos, wide);
            let offset = read_u32(bytecode, &mut pos);
            Instruction::MovFromStack { dst, offset }
        }
        Op::MovToTemp => {
            let array_idx = read_u16(bytecode, &mut pos);
            let idx = read_u16(bytecode, &mut pos);
            let src = read_reg(bytecode, &mut pos, wide);
            Instruction::MovToTemp {
                array_idx,
                idx,
                src,
            }
        }
        Op::MovFromTemp => {
            let dst = read_reg(bytecode, &mut pos, wide);
            let array_idx = read_u16(bytecode, &mut pos);
            let idx = read_u16(bytecode, &mut pos);
            Instruction::MovFromTemp {
                dst,
                array_idx,
                idx,
            }
        }
        Op::MovToAssoc => {
            let idx = read_u16(bytecode, &mut pos);
            let src = read_reg(bytecode, &mut pos, wide);
            Instruction::MovToAssoc { idx, src }
        }
        Op::MovFromAssoc => {
            let dst = read_reg(bytecode, &mut pos, wide);
            let idx = read_u16(bytecode, &mut pos);
            Instruction::MovFromAssoc { dst, idx }
        }
        Op::Jump => Instruction::Jump {
            offset: read_i16(bytecode, &mut pos),
        },
        Op::JumpIfTrue => Instruction::JumpIfTrue {
            offset: read_i16(bytecode, &mut pos),
        },
        Op::JumpIfFalse => Instruction::JumpIfFalse {
            offset: read_i16(bytecode, &mut pos),
        },
        Op::Resend => {
            let message_idx = read_u16(bytecode, &mut pos);
            let reg = read_reg(bytecode, &mut pos, wide);
            let argc = read_u8(bytecode, &mut pos);
            let feedback_idx = read_u16(bytecode, &mut pos);
            Instruction::Resend {
                message_idx,
                reg,
                argc,
                feedback_idx,
            }
        }
        Op::DirectedResend => {
            let message_idx = read_u16(bytecode, &mut pos);
            let reg = read_reg(bytecode, &mut pos, wide);
            let argc = read_u8(bytecode, &mut pos);
            let feedback_idx = read_u16(bytecode, &mut pos);
            let delegate_idx = read_u16(bytecode, &mut pos);
            Instruction::DirectedResend {
                message_idx,
                reg,
                argc,
                feedback_idx,
                delegate_idx,
            }
        }
        Op::Wide | Op::ExtraWide => unsafe {
            std::hint::unreachable_unchecked()
        },
    };

    (instr, pos)
}

fn read_u8(bytes: &[u8], pos: &mut usize) -> u8 {
    let value = bytes[*pos];
    *pos += 1;
    value
}

fn read_u16(bytes: &[u8], pos: &mut usize) -> u16 {
    let slice = &bytes[*pos..*pos + 2];
    *pos += 2;
    u16::from_le_bytes(slice.try_into().unwrap())
}

fn read_i16(bytes: &[u8], pos: &mut usize) -> i16 {
    read_u16(bytes, pos) as i16
}

fn read_u32(bytes: &[u8], pos: &mut usize) -> u32 {
    let slice = &bytes[*pos..*pos + 4];
    *pos += 4;
    u32::from_le_bytes(slice.try_into().unwrap())
}

fn read_i32(bytes: &[u8], pos: &mut usize) -> i32 {
    read_u32(bytes, pos) as i32
}

fn read_reg(bytes: &[u8], pos: &mut usize, wide: bool) -> u16 {
    if wide {
        read_u16(bytes, pos)
    } else {
        read_u8(bytes, pos) as u16
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::compiler0::Compiler;
    use crate::materialize::materialize;
    use crate::special::bootstrap;
    use crate::USER_MODULE;
    use heap::HeapSettings;
    use object::{Array, Header, Map, ObjectType, SlotFlags, VMString};
    use parser::{Lexer, Parser};

    #[repr(C)]
    struct TestPair {
        a: i32,
        b: i32,
    }

    extern "C" fn ffi_sum_pair(pair: TestPair) -> i32 {
        pair.a + pair.b
    }

    extern "C" fn ffi_make_pair(a: i32, b: i32) -> TestPair {
        TestPair { a, b }
    }

    fn test_settings() -> HeapSettings {
        HeapSettings {
            heap_size: 1024 * 1024,
            block_size: 8192,
            large_size: 4096 - 16,
            line_size: 64,
            bytes_before_gc: 0.1,
            nursery_fraction: 0.1,
            minor_recycle_threshold: 0.5,
            max_minor_before_major: 3,
        }
    }

    fn parse_source(src: &str) -> (parser::AstArena, Vec<parser::ExprId>) {
        let lexer = Lexer::from_str(src);
        let mut parser = Parser::new(lexer);
        let parsed: Vec<_> = parser.by_ref().collect();
        let arena = parser.into_arena();
        let exprs = parsed
            .into_iter()
            .map(|r| r.expect("parse error"))
            .collect();
        (arena, exprs)
    }

    fn run_source(src: &str) -> Result<Value, LocatedRuntimeError> {
        let (arena, exprs) = parse_source(src);
        let mut vm = bootstrap(test_settings());
        vm.open_module(USER_MODULE);
        let code_desc = Compiler::compile_for_vm_ids(&vm, &arena, &exprs)
            .expect("compile error");
        let code_val = materialize(&mut vm, &code_desc);
        interpret(&mut vm, code_val)
    }

    fn run_source_with_vm(
        src: &str,
    ) -> Result<(VM, Value), LocatedRuntimeError> {
        let (arena, exprs) = parse_source(src);
        let mut vm = bootstrap(test_settings());
        vm.open_module(USER_MODULE);
        let code_desc = Compiler::compile_for_vm_ids(&vm, &arena, &exprs)
            .expect("compile error");
        let code_val = materialize(&mut vm, &code_desc);
        let value = interpret(&mut vm, code_val)?;
        Ok((vm, value))
    }

    fn run_source_with_receiver(
        src: &str,
        receiver: Value,
    ) -> Result<Value, LocatedRuntimeError> {
        let (arena, exprs) = parse_source(src);
        let mut vm = bootstrap(test_settings());
        vm.open_module(USER_MODULE);
        let code_desc = Compiler::compile_for_vm_ids(&vm, &arena, &exprs)
            .expect("compile error");
        let code_val = materialize(&mut vm, &code_desc);
        interpret_with_receiver(&mut vm, code_val, receiver)
    }

    #[test]
    fn interpret_fixnum_literal() {
        let value = run_source("42").expect("interpret error");
        assert!(value.is_fixnum());
        assert_eq!(unsafe { value.to_i64() }, 42);
    }

    #[test]
    fn interpret_string_literal() {
        let (_vm, value) =
            run_source_with_vm("\"hello\"").expect("interpret error");
        assert!(value.is_ref());
        let s: &VMString = unsafe { value.as_ref() };
        assert_eq!(unsafe { s.as_str() }, "hello");
    }

    #[test]
    fn interpret_self() {
        let receiver = Value::from_i64(99);
        let value = run_source_with_receiver("self", receiver)
            .expect("interpret error");
        assert_eq!(value.raw(), receiver.raw());
    }

    #[test]
    fn global_assign_visible_inside_closure_assignment() {
        let value = run_source("g := 1. [ g := g _FixnumAdd: 1 ] call. g")
            .expect("interpret error");
        assert!(value.is_fixnum());
        assert_eq!(unsafe { value.to_i64() }, 2);
    }

    #[test]
    fn send_populates_feedback_vector_entry() {
        let mut vm = bootstrap(test_settings());
        let code_desc = crate::compiler0::CodeDesc {
            bytecode: vec![Op::LocalReturn as u8],
            constants: vec![],
            register_count: 1,
            arg_count: 0,
            temp_count: 0,
            feedback_count: 1,
            source_map: vec![],
        };
        let code_val = materialize(&mut vm, &code_desc);

        let mut state = InterpreterState {
            acc: vm.special.none,
            frames: Vec::new(),
            register_stack: Vec::new(),
            register_top: 0,
            handlers: Vec::new(),
            finalizers: Vec::new(),
            pending_restores: Vec::new(),
            unwind_cleanup_depths: Vec::new(),
            unwind: None,
            last_pc: 0,
            last_code: code_val,
        };

        let code: &Code = unsafe { code_val.as_ref() };
        let receiver_feedback_map = vm.special.fixnum_traits;
        let megamorphic_key =
            megamorphic_key_for_send(vm.special.none, receiver_feedback_map);
        let receiver = Value::from_i64(1);
        let holder = vm.special.object;
        update_send_feedback_entry(
            &mut vm,
            &mut state,
            code,
            0,
            megamorphic_key,
            receiver,
            receiver_feedback_map,
            holder,
            0,
            false,
        )
        .expect("feedback update should succeed");

        unsafe {
            let code: &Code = code_val.as_ref();
            assert!(code.feedback.is_ref());
            let feedback: &Array = code.feedback.as_ref();
            assert_eq!(feedback.len(), 1);
            let entry = feedback.element(0);
            let header: &Header = entry.as_ref();
            assert_eq!(header.object_type(), ObjectType::Array);
            let polymorphic: &Array = entry.as_ref();
            assert_eq!(polymorphic.len(), FEEDBACK_ENTRY_STRIDE as u64);
            assert_eq!(
                polymorphic.element(FEEDBACK_ENTRY_MAP_IDX as u64).raw(),
                vm.special.fixnum_traits.raw()
            );
        }
    }

    #[test]
    fn interpret_local_assignment() {
        let value = run_source("x = 5. x").expect("interpret error");
        assert!(value.is_fixnum());
        assert_eq!(unsafe { value.to_i64() }, 5);
    }

    #[test]
    fn interpret_global_store_load() {
        let value = run_source("Y := 5. Y").expect("interpret error");
        assert!(value.is_fixnum());
        assert_eq!(unsafe { value.to_i64() }, 5);
    }

    #[test]
    fn interpret_data_object_creation() {
        let (_vm, value) =
            run_source_with_vm("{ x = 5 }").expect("interpret error");
        assert!(value.is_ref());
        let obj: &SlotObject = unsafe { value.as_ref() };
        assert_eq!(obj.header.object_type(), ObjectType::Slots);
        let map: &Map = unsafe { obj.map.as_ref() };
        assert_eq!(map.slot_count(), 1);
        let slot = unsafe { map.slot(0) };
        assert!(slot.flags().contains(SlotFlags::CONSTANT));
        assert_eq!(unsafe { slot.value.to_i64() }, 5);
    }

    #[test]
    fn interpret_lookup_constant_slot() {
        let value = run_source("{ x = 5 } x").expect("interpret error");
        assert!(value.is_fixnum());
        assert_eq!(unsafe { value.to_i64() }, 5);
    }

    #[test]
    fn interpret_lookup_assignable_slot() {
        let value = run_source("{ x := 5 } x").expect("interpret error");
        assert!(value.is_fixnum());
        assert_eq!(unsafe { value.to_i64() }, 5);
    }

    #[test]
    fn interpret_lookup_assignment_slot() {
        let value =
            run_source("o = { x := 0 }. o x: 7. o x").expect("interpret error");
        assert!(value.is_fixnum());
        assert_eq!(unsafe { value.to_i64() }, 7);
    }

    #[test]
    fn interpret_method_activation() {
        let value =
            run_source("o = { foo = { 42 } }. o foo").expect("interpret error");
        assert!(value.is_fixnum());
        assert_eq!(unsafe { value.to_i64() }, 42);
    }

    #[test]
    fn interpret_nested_send() {
        let value =
            run_source("o = { foo = { self bar }. bar = { 7 } }. o foo")
                .expect("interpret error");
        assert!(value.is_fixnum());
        assert_eq!(unsafe { value.to_i64() }, 7);
    }

    #[test]
    fn interpret_block_creation() {
        let (_vm, value) = run_source_with_vm("[1]").expect("interpret error");
        assert!(value.is_ref());
        let header: &Header = unsafe { value.as_ref() };
        assert_eq!(header.object_type(), ObjectType::Block);
    }

    #[test]
    fn interpret_message_not_understood() {
        let err = run_source("5 foo").expect_err("expected error");
        assert!(matches!(
            err.error,
            RuntimeError::MessageNotUnderstood { .. }
        ));
    }

    #[test]
    fn interpret_temp_store_load() {
        let value = run_source("x = 5. [ x ]. x").expect("interpret error");
        assert!(value.is_fixnum());
        assert_eq!(unsafe { value.to_i64() }, 5);
    }

    #[test]
    fn interpret_while_true_block_capture() {
        let result = run_source_with_vm(
            "Object _Extend: Object With: { \
                extend: target With: source = { self _Extend: target With: source } \
            }. \
            Object extend: Object With: { \
                ifTrue: t IfFalse: f = { t call }. \
                ifTrue: t = { self ifTrue: t IfFalse: [ None ] }. \
                ifFalse: f = { self ifTrue: [ None ] IfFalse: f } \
            }. \
            Object extend: False With: { \
                parent* = Object. \
                ifTrue: t IfFalse: f = { f call } \
            }. \
            Object extend: True With: { parent* = Object }. \
            Object extend: Fixnum With: { \
                parent* = Object. \
                <= rhs = { rhs leFixnum: self }. \
                leFixnum: lhs = { lhs _FixnumLe: self }. \
                + rhs = { rhs addFixnum: self }. \
                addFixnum: lhs = { lhs _FixnumAdd: self } \
            }. \
            Object extend: Block With: { \
                parent* = Object. \
                whileTrue: body = { \
                    self call ifTrue: [ \
                        body call. \
                        self whileTrue: body \
                    ] IfFalse: [ None ] \
                } \
            }. \
            [ i := 0. cond := [ i <= 1 ]. cond whileTrue: [ i := i + 1 ] ] call",
        );
        let (vm, value) = result.expect("interpret error");
        assert_eq!(value.raw(), vm.special.none.raw());
    }

    #[test]
    fn while_true_deep_recursion_does_not_overflow_with_tco() {
        let src =
            "Object _Extend: Object With: { \
                extend: target With: source = { self _Extend: target With: source } \
            }. \
            Object extend: Object With: { \
                ifTrue: t IfFalse: f = { t call }. \
                ifTrue: t = { self ifTrue: t IfFalse: [ None ] }. \
                ifFalse: f = { self ifTrue: [ None ] IfFalse: f } \
            }. \
            Object extend: False With: { \
                parent* = Object. \
                ifTrue: t IfFalse: f = { f call } \
            }. \
            Object extend: True With: { parent* = Object }. \
            Object extend: Fixnum With: { \
                parent* = Object. \
                <= rhs = { rhs leFixnum: self }. \
                leFixnum: lhs = { lhs _FixnumLe: self }. \
                + rhs = { rhs addFixnum: self }. \
                addFixnum: lhs = { lhs _FixnumAdd: self } \
            }. \
            Object extend: Block With: { \
                parent* = Object. \
                whileTrue: body = { \
                    self call ifTrue: [ \
                        body call. \
                        self whileTrue: body \
                    ] IfFalse: [ None ] \
                } _EnsureTailCall \
            }. \
            [ i := 0. cond := [ i <= 2000 ]. cond whileTrue: [ i := i + 1 ] ] call";

        let (vm, value) = run_source_with_vm(src).expect("interpret error");
        assert_eq!(value.raw(), vm.special.none.raw());
    }

    #[test]
    fn interpret_nested_temp_chain() {
        let value = run_source(
            "[ i := 0. [ j := 1. [ i := i _FixnumAdd: j ] call. i ] call ] call",
        )
        .expect("interpret error");
        assert!(value.is_fixnum());
        assert_eq!(unsafe { value.to_i64() }, 1);
    }

    #[test]
    fn interpret_method_block_captures_local() {
        let src = "
            Obj = { \
                foo = { \
                    x = 1. \
                    [ x ] call \
                } \
            }. \
            Obj foo";
        let value = run_source(src).expect("interpret error");
        assert!(value.is_fixnum());
        assert_eq!(unsafe { value.to_i64() }, 1);
    }

    #[test]
    fn extend_block_adds_while_true() {
        let (vm, _value) = run_source_with_vm(
            "Object _Extend: Object With: { \
                extend: target With: source = { self _Extend: target With: source } \
            }. \
            Object extend: Block With: { \
                parent* = Object. \
                whileTrue: body = { None } \
            }. \
            None",
        )
        .expect("interpret error");

        let block_traits = vm.special.block_traits;
        let obj: &SlotObject = unsafe { block_traits.as_ref() };
        let map: &Map = unsafe { obj.map.as_ref() };
        let mut found = false;
        for slot in unsafe { map.slots() } {
            let name: &VMString = unsafe { slot.name.as_ref() };
            if unsafe { name.as_str() } == "whileTrue:" {
                found = true;
                break;
            }
        }
        assert!(found, "whileTrue: slot not found on Block");
    }

    #[test]
    fn while_true_method_slot_is_tail_call_method_object() {
        let (vm, _value) = run_source_with_vm(
            "Object _Extend: Object With: { \
                extend: target With: source = { self _Extend: target With: source } \
            }. \
            Object extend: Block With: { \
                parent* = Object. \
                whileTrue: body = { \
                    self call ifTrue: [ \
                        body call. \
                        self whileTrue: body \
                    ] IfFalse: [ None ] \
                } _EnsureTailCall \
            }. \
            None",
        )
        .expect("interpret error");

        let block_traits = vm.special.block_traits;
        let obj: &SlotObject = unsafe { block_traits.as_ref() };
        let map: &Map = unsafe { obj.map.as_ref() };

        let while_true_slot = unsafe { map.slots() }
            .iter()
            .find(|slot| {
                let name: &VMString = unsafe { slot.name.as_ref() };
                let slot_name = unsafe { name.as_str() };
                slot_name == "whileTrue:"
            })
            .expect("whileTrue: slot missing on Block");

        assert!(while_true_slot.value.is_ref());
        let method_header: &Header = unsafe { while_true_slot.value.as_ref() };
        assert_eq!(method_header.object_type(), ObjectType::Slots);

        let method_obj: &SlotObject = unsafe { while_true_slot.value.as_ref() };
        let method_map: &Map = unsafe { method_obj.map.as_ref() };
        assert!(method_map.has_code());
        assert!(method_map.is_tail_call());
    }

    #[test]
    fn block_literal_returns_block() {
        let (_vm, value) =
            run_source_with_vm("i := 0. cond := [ i <= 1 ]. cond")
                .expect("interpret error");
        let header: &Header = unsafe { value.as_ref() };
        assert_eq!(header.object_type(), ObjectType::Block);
    }

    #[test]
    fn setup_with_while_true_installs_slot() {
        let (vm, value) = run_source_with_vm(
            "Object _Extend: Object With: { \
                extend: target With: source = { self _Extend: target With: source } \
            }. \
            Object extend: Object With: { \
                ifTrue: t IfFalse: f = { t call }. \
                ifTrue: t = { self ifTrue: t IfFalse: [ None ] }. \
                ifFalse: f = { self ifTrue: [ None ] IfFalse: f } \
            }. \
            Object extend: False With: { \
                parent* = Object. \
                ifTrue: t IfFalse: f = { f call } \
            }. \
            Object extend: True With: { parent* = Object }. \
            Object extend: Block With: { \
                parent* = Object. \
                whileTrue: body = { \
                    self call ifTrue: [ \
                        body call. \
                        self whileTrue: body \
                    ] IfFalse: [ None ] \
                } \
            }. \
            i := 0. cond := [ i <= 1 ]. cond",
        )
        .expect("interpret error");

        let header: &Header = unsafe { value.as_ref() };
        assert_eq!(header.object_type(), ObjectType::Block);

        let block_traits = vm.special.block_traits;
        let obj: &SlotObject = unsafe { block_traits.as_ref() };
        let map: &Map = unsafe { obj.map.as_ref() };
        let mut found = false;
        for slot in unsafe { map.slots() } {
            let name: &VMString = unsafe { slot.name.as_ref() };
            if unsafe { name.as_str() } == "whileTrue:" {
                found = true;
                break;
            }
        }
        assert!(found, "whileTrue: slot not found on Block");
    }

    #[test]
    fn interpret_simple_while_true_call() {
        let value = run_source(
            "Object _Extend: Object With: { \
                extend: target With: source = { self _Extend: target With: source } \
            }. \
            Object extend: Block With: { \
                parent* = Object. \
                whileTrue: body = { None } \
            }. \
            cond := [ 1 ]. cond whileTrue: [ None ]",
        )
        .expect("interpret error");
        assert!(value.is_ref());
    }

    #[test]
    fn interpret_top_level_const_assoc_lookup() {
        let value = run_source("Math = { foo = { 1 }. }. Math foo")
            .expect("interpret error");
        assert!(value.is_fixnum());
        assert_eq!(unsafe { value.to_i64() }, 1);
    }

    #[test]
    fn clone_available_via_parent() {
        let src = "
            Object _Extend: Object With: {
                extend: target With: source = { self _Extend: target With: source }
            }.
            Object extend: Object With: { clone = { 1 } }.
            Complex = { parent* = Object }.
            Complex clone
        ";
        let value = run_source(src).expect("interpret error");
        assert!(value.is_fixnum());
        assert_eq!(unsafe { value.to_i64() }, 1);
    }

    #[test]
    fn array_extend_runtime_parent_slot_is_resolved_at_runtime() {
        let value = run_source(
            "Seq = { ping = { 7 } }. Object _Extend: Array With: { parent* = Seq }. a := Array _ArrayCloneWithSize: 0. a ping",
        )
        .expect("interpret error");
        assert!(value.is_fixnum());
        assert_eq!(unsafe { value.to_i64() }, 7);
    }

    #[test]
    fn top_level_const_assoc_value_is_object() {
        let (vm, _) = run_source_with_vm("Math = { foo = { 1 }. }.")
            .expect("interpret error");
        let assoc_val =
            lookup_dictionary_value(&vm, "Math").expect("Math assoc not found");
        assert_ne!(assoc_val.raw(), vm.special.none.raw());
        let header: &Header = unsafe { assoc_val.as_ref() };
        assert_eq!(header.object_type(), ObjectType::Slots);
        let obj: &SlotObject = unsafe { assoc_val.as_ref() };
        let obj_map: &Map = unsafe { obj.map.as_ref() };
        unsafe {
            assert!(!obj_map.slots().is_empty());
        }
    }

    #[test]
    fn interpret_block_updates_captured_mutable() {
        let value =
            run_source("[ x := 0. [ x := x _FixnumAdd: 1 ] call. x ] call")
                .expect("interpret error");
        assert!(value.is_fixnum());
        assert_eq!(unsafe { value.to_i64() }, 1);
    }

    #[test]
    fn interpret_nested_block_reads_capture() {
        let value = run_source("[ x := 0. [ [ x ] call ] call ] call")
            .expect("interpret error");
        assert!(value.is_fixnum());
        assert_eq!(unsafe { value.to_i64() }, 0);
    }

    #[test]
    fn interpret_block_le_on_capture() {
        let (vm, value) = run_source_with_vm(
            "Object _Extend: Fixnum With: { \
                <= rhs = { rhs leFixnum: self }. \
                leFixnum: lhs = { lhs _FixnumLe: self } \
            }. \
            [ i := 0. [ i <= 1 ] call ] call",
        )
        .expect("interpret error");
        assert_eq!(value.raw(), vm.special.true_obj.raw());
    }

    #[test]
    fn interpret_non_local_return() {
        let value = run_source("^ 42").expect("interpret error");
        assert!(value.is_fixnum());
        assert_eq!(unsafe { value.to_i64() }, 42);
    }

    #[test]
    fn signal_resumes_in_place() {
        let value = run_source(
            "(VM _WithHandler: [ | condition | condition _FixnumAdd: 1 ] Do: [ VM _Signal: 41 ]) _FixnumAdd: 1",
        )
        .expect("interpret error");
        assert!(value.is_fixnum());
        assert_eq!(unsafe { value.to_i64() }, 43);
    }

    #[test]
    fn handler_can_request_unwind() {
        let value = run_source(
            "VM _WithHandler: [ | condition | VM _Unwind: (condition _FixnumAdd: 1) ] Do: [ VM _Signal: 41. 0 ]",
        )
        .expect("interpret error");
        assert!(value.is_fixnum());
        assert_eq!(unsafe { value.to_i64() }, 42);
    }

    #[test]
    fn then_runs_cleanup_on_normal_return() {
        let value = run_source(
            "VM _WithHandler: [ | c | c ] Do: [ VM _Then: [ 7 ] Do: [ VM _Unwind: 99 ] ]",
        )
        .expect("interpret error");
        assert!(value.is_fixnum());
        assert_eq!(unsafe { value.to_i64() }, 99);
    }

    #[test]
    fn then_runs_cleanup_on_unwind() {
        let value = run_source(
            "VM _WithHandler: [ | c | c ] Do: [ VM _Then: [ VM _Unwind: 7. 0 ] Do: [ VM _Unwind: 99 ] ]",
        )
        .expect("interpret error");
        assert!(value.is_fixnum());
        assert_eq!(unsafe { value.to_i64() }, 99);
    }

    fn lookup_dictionary_value(vm: &VM, name: &str) -> Option<Value> {
        if let Some(value) = vm.module_lookup_in(USER_MODULE, name) {
            return Some(value);
        }

        let sym = vm.with_intern_table(|table| table.get(name).copied())?;
        unsafe {
            let dict_obj: &SlotObject = vm.dictionary.as_ref();
            let map: &Map = dict_obj.map.as_ref();
            for slot in map.slots() {
                if slot.name.raw() == sym.raw() {
                    let assoc_obj: &SlotObject = slot.value.as_ref();
                    return Some(
                        assoc_obj.read_value(SlotObject::VALUES_OFFSET),
                    );
                }
            }
        }
        None
    }

    #[test]
    fn interpret_fixnum_add_primitive() {
        let value = run_source("1 _FixnumAdd: 2").expect("interpret error");
        assert!(value.is_fixnum());
        assert_eq!(unsafe { value.to_i64() }, 3);
    }

    #[test]
    fn fixnum_traits_primitive_slot() {
        let vm = bootstrap(test_settings());
        let fixnum_traits = vm.special.fixnum_traits;
        let obj: &SlotObject = unsafe { fixnum_traits.as_ref() };
        let map: &Map = unsafe { obj.map.as_ref() };
        let mut found = false;
        for slot in unsafe { map.slots() } {
            let name: &VMString = unsafe { slot.name.as_ref() };
            if unsafe { name.as_str() } != "_FixnumAdd:" {
                continue;
            }
            found = true;
            let method_obj: &SlotObject = unsafe { slot.value.as_ref() };
            let method_map: &Map = unsafe { method_obj.map.as_ref() };
            assert!(method_map.has_code());
            assert!(method_map.is_primitive());
            assert!(method_map.code.is_fixnum());
            let idx = unsafe { method_map.code.to_i64() } as usize;
            let prim = vm.primitives.get(idx).expect("primitive index");
            assert_eq!(prim.name, "fixnum_add");
            assert_eq!(prim.arity, 1);
        }
        assert!(found, "_FixnumAdd: slot not found");
    }

    #[test]
    fn array_traits_primitive_slot() {
        let vm = bootstrap(test_settings());
        let traits_obj: &SlotObject =
            unsafe { vm.special.array_traits.as_ref() };
        let map: &Map = unsafe { traits_obj.map.as_ref() };
        let mut found = false;
        for slot in unsafe { map.slots() } {
            let name: &VMString = unsafe { slot.name.as_ref() };
            if unsafe { name.as_str() } != "_ArrayAt:Put:" {
                continue;
            }
            found = true;
            let method_obj: &SlotObject = unsafe { slot.value.as_ref() };
            let method_map: &Map = unsafe { method_obj.map.as_ref() };
            assert!(method_map.has_code());
            assert!(method_map.is_primitive());
            let idx = unsafe { method_map.code.to_i64() } as usize;
            let prim = vm.primitives.get(idx).expect("primitive index");
            assert_eq!(prim.name, "array_at_put");
        }
        assert!(found, "_ArrayAt:Put: slot not found");
    }

    #[test]
    fn array_primitives_basic_behavior() {
        let value = run_source(
            "arr := Array _ArrayCloneWithSize: 2. arr _ArrayAt: 0 Put: 41. arr _ArrayAt: 1 Put: 1. (arr _ArrayAt: 0) _FixnumAdd: (arr _ArrayAt: 1)",
        )
        .expect("interpret error");
        assert!(value.is_fixnum());
        assert_eq!(unsafe { value.to_i64() }, 42);
    }

    #[test]
    fn array_clone_with_size_initializes_to_none() {
        let (vm, value) = run_source_with_vm(
            "arr := Array _ArrayCloneWithSize: 1. arr _ArrayAt: 0",
        )
        .expect("interpret error");
        assert_eq!(value.raw(), vm.special.none.raw());
    }

    #[test]
    fn array_at_out_of_bounds_is_error() {
        let err =
            run_source("arr := Array _ArrayCloneWithSize: 1. arr _ArrayAt: 1")
                .expect_err("expected error");
        assert!(matches!(
            err.error,
            RuntimeError::Unimplemented {
                message: "array index out of bounds"
            }
        ));
    }

    #[test]
    fn array_at_put_negative_index_is_error() {
        let err = run_source(
            "arr := Array _ArrayCloneWithSize: 1. arr _ArrayAt: -1 Put: 5",
        )
        .expect_err("expected error");
        assert!(matches!(
            err.error,
            RuntimeError::Unimplemented {
                message: "array index must be non-negative"
            }
        ));
    }

    #[test]
    fn bignum_traits_primitive_slot() {
        let vm = bootstrap(test_settings());
        let traits_obj: &SlotObject =
            unsafe { vm.special.bignum_traits.as_ref() };
        let map: &Map = unsafe { traits_obj.map.as_ref() };
        let mut found = false;
        for slot in unsafe { map.slots() } {
            let name: &VMString = unsafe { slot.name.as_ref() };
            if unsafe { name.as_str() } != "_BignumAdd:" {
                continue;
            }
            found = true;
            let method_obj: &SlotObject = unsafe { slot.value.as_ref() };
            let method_map: &Map = unsafe { method_obj.map.as_ref() };
            assert!(method_map.has_code());
            assert!(method_map.is_primitive());
            let idx = unsafe { method_map.code.to_i64() } as usize;
            let prim = vm.primitives.get(idx).expect("primitive index");
            assert_eq!(prim.name, "bignum_add");
        }
        assert!(found, "_BignumAdd: slot not found");
    }

    #[test]
    fn ratio_traits_primitive_slot() {
        let vm = bootstrap(test_settings());
        let traits_obj: &SlotObject =
            unsafe { vm.special.ratio_traits.as_ref() };
        let map: &Map = unsafe { traits_obj.map.as_ref() };
        let mut found = false;
        for slot in unsafe { map.slots() } {
            let name: &VMString = unsafe { slot.name.as_ref() };
            if unsafe { name.as_str() } != "_RatioAdd:" {
                continue;
            }
            found = true;
            let method_obj: &SlotObject = unsafe { slot.value.as_ref() };
            let method_map: &Map = unsafe { method_obj.map.as_ref() };
            assert!(method_map.has_code());
            assert!(method_map.is_primitive());
            let idx = unsafe { method_map.code.to_i64() } as usize;
            let prim = vm.primitives.get(idx).expect("primitive index");
            assert_eq!(prim.name, "ratio_add");
        }
        assert!(found, "_RatioAdd: slot not found");
    }

    #[test]
    fn float_traits_primitive_slot() {
        let vm = bootstrap(test_settings());
        let traits_obj: &SlotObject =
            unsafe { vm.special.float_traits.as_ref() };
        let map: &Map = unsafe { traits_obj.map.as_ref() };
        let mut found = false;
        for slot in unsafe { map.slots() } {
            let name: &VMString = unsafe { slot.name.as_ref() };
            if unsafe { name.as_str() } != "_FloatAdd:" {
                continue;
            }
            found = true;
            let method_obj: &SlotObject = unsafe { slot.value.as_ref() };
            let method_map: &Map = unsafe { method_obj.map.as_ref() };
            assert!(method_map.has_code());
            assert!(method_map.is_primitive());
            let idx = unsafe { method_map.code.to_i64() } as usize;
            let prim = vm.primitives.get(idx).expect("primitive index");
            assert_eq!(prim.name, "float_add");
        }
        assert!(found, "_FloatAdd: slot not found");
    }

    #[test]
    fn alien_traits_primitive_slot() {
        let vm = bootstrap(test_settings());
        let traits_obj: &SlotObject =
            unsafe { vm.special.alien_traits.as_ref() };
        let map: &Map = unsafe { traits_obj.map.as_ref() };
        let mut found = false;
        for slot in unsafe { map.slots() } {
            let name: &VMString = unsafe { slot.name.as_ref() };
            if unsafe { name.as_str() } != "_AlienNew:" {
                continue;
            }
            found = true;
            let method_obj: &SlotObject = unsafe { slot.value.as_ref() };
            let method_map: &Map = unsafe { method_obj.map.as_ref() };
            assert!(method_map.has_code());
            assert!(method_map.is_primitive());
            let idx = unsafe { method_map.code.to_i64() } as usize;
            let prim = vm.primitives.get(idx).expect("primitive index");
            assert_eq!(prim.name, "alien_new");
            assert_eq!(prim.arity, 1);
        }
        assert!(found, "_AlienNew: slot not found");
    }

    #[test]
    fn alien_primitives_allocate_write_read_free() {
        let value = run_source(
            "a := Alien _AlienNew: 8. a _AlienU64At: 0 Put: 123. v := a _AlienU64At: 0. a _AlienFree. v",
        )
        .expect("interpret error");
        assert!(value.is_fixnum());
        assert_eq!(unsafe { value.to_i64() }, 123);
    }

    #[test]
    fn compare_fixnum_primitives() {
        let (vm, value) =
            run_source_with_vm("1 _FixnumEq: 1").expect("interpret error");
        assert_eq!(value.raw(), vm.special.true_obj.raw());

        let (vm, value) =
            run_source_with_vm("1 _FixnumLt: 2").expect("interpret error");
        assert_eq!(value.raw(), vm.special.true_obj.raw());

        let (vm, value) =
            run_source_with_vm("2 _FixnumGt: 3").expect("interpret error");
        assert_eq!(value.raw(), vm.special.false_obj.raw());
    }

    #[test]
    fn compare_bignum_primitives() {
        let (vm, value) = run_source_with_vm(
            "(1 _FixnumToBignum) _BignumLt: (2 _FixnumToBignum)",
        )
        .expect("interpret error");
        assert_eq!(value.raw(), vm.special.true_obj.raw());
    }

    #[test]
    fn compare_ratio_primitives() {
        let (vm, value) =
            run_source_with_vm("(1 _FixnumDiv: 2) _RatioLt: (1 _FixnumDiv: 3)")
                .expect("interpret error");
        assert_eq!(value.raw(), vm.special.false_obj.raw());
    }

    #[test]
    fn compare_float_primitives() {
        let (vm, value) =
            run_source_with_vm("1.0 _FloatApproxEq: 1.0001 WithEpsilon: 0.001")
                .expect("interpret error");
        assert_eq!(value.raw(), vm.special.true_obj.raw());
    }

    #[test]
    fn dictionary_has_object_binding() {
        let vm = bootstrap(test_settings());
        let object_value =
            lookup_dictionary_value(&vm, "Object").expect("Object missing");
        let object_obj: &SlotObject = unsafe { object_value.as_ref() };
        let object_map: &Map = unsafe { object_obj.map.as_ref() };
        let mut found = false;
        for slot in unsafe { object_map.slots() } {
            let name: &VMString = unsafe { slot.name.as_ref() };
            if unsafe { name.as_str() } == "_Extend:With:" {
                found = true;
                break;
            }
        }
        assert!(found, "Object missing _Extend:With:");
    }

    #[test]
    fn object_has_reflect_primitive_slot() {
        let vm = bootstrap(test_settings());
        let object_value =
            lookup_dictionary_value(&vm, "Object").expect("Object missing");
        let object_obj: &SlotObject = unsafe { object_value.as_ref() };
        let map: &Map = unsafe { object_obj.map.as_ref() };
        let mut found = false;
        for slot in unsafe { map.slots() } {
            let name: &VMString = unsafe { slot.name.as_ref() };
            if unsafe { name.as_str() } != "_Reflect:" {
                continue;
            }
            found = true;
            let method_obj: &SlotObject = unsafe { slot.value.as_ref() };
            let method_map: &Map = unsafe { method_obj.map.as_ref() };
            assert!(method_map.has_code());
            assert!(method_map.is_primitive());
            let idx = unsafe { method_map.code.to_i64() } as usize;
            let prim = vm.primitives.get(idx).expect("primitive index");
            assert_eq!(prim.name, "object_reflect");
            assert_eq!(prim.arity, 1);
        }
        assert!(found, "_Reflect: slot not found");
    }

    #[test]
    fn object_has_become_with_primitive_slot() {
        let vm = bootstrap(test_settings());
        let object_value =
            lookup_dictionary_value(&vm, "Object").expect("Object missing");
        let object_obj: &SlotObject = unsafe { object_value.as_ref() };
        let map: &Map = unsafe { object_obj.map.as_ref() };
        let mut found = false;
        for slot in unsafe { map.slots() } {
            let name: &VMString = unsafe { slot.name.as_ref() };
            if unsafe { name.as_str() } != "_Become:With:" {
                continue;
            }
            found = true;
            let method_obj: &SlotObject = unsafe { slot.value.as_ref() };
            let method_map: &Map = unsafe { method_obj.map.as_ref() };
            assert!(method_map.has_code());
            assert!(method_map.is_primitive());
            let idx = unsafe { method_map.code.to_i64() } as usize;
            let prim = vm.primitives.get(idx).expect("primitive index");
            assert_eq!(prim.name, "object_become_with");
            assert_eq!(prim.arity, 2);
        }
        assert!(found, "_Become:With: slot not found");
    }

    #[test]
    fn object_has_ctype_primitives() {
        let vm = bootstrap(test_settings());
        let object_value =
            lookup_dictionary_value(&vm, "Object").expect("Object missing");
        let object_obj: &SlotObject = unsafe { object_value.as_ref() };
        let map: &Map = unsafe { object_obj.map.as_ref() };
        let mut saw_build = false;
        let mut saw_info = false;
        let mut saw_tag = false;
        for slot in unsafe { map.slots() } {
            let name: &VMString = unsafe { slot.name.as_ref() };
            match unsafe { name.as_str() } {
                "_CTypeBuildStruct:" => saw_build = true,
                "_CTypeFieldInfoAt:" => saw_info = true,
                "_CTypeScalarTag" => saw_tag = true,
                _ => {}
            }
        }
        assert!(saw_build, "_CTypeBuildStruct: slot not found");
        assert!(saw_info, "_CTypeFieldInfoAt: slot not found");
        assert!(saw_tag, "_CTypeScalarTag slot not found");
    }

    #[test]
    fn vm_has_platform_thread_primitives() {
        let vm = bootstrap(test_settings());
        let vm_value = lookup_dictionary_value(&vm, "VM").expect("VM missing");
        let vm_obj: &SlotObject = unsafe { vm_value.as_ref() };
        let map: &Map = unsafe { vm_obj.map.as_ref() };

        let mut saw_spawn = false;
        let mut saw_join = false;
        let mut saw_current = false;
        let mut saw_yield = false;
        let mut saw_park = false;
        let mut saw_park_for = false;
        let mut saw_unpark = false;
        let mut saw_millis = false;
        let mut saw_unix_time = false;

        for slot in unsafe { map.slots() } {
            let name: &VMString = unsafe { slot.name.as_ref() };
            let slot_name = unsafe { name.as_str() };
            let expect = match slot_name {
                "_SpawnPlatform:" => Some(("vm_spawn_platform", 1)),
                "_ThreadJoin:" => Some(("vm_thread_join", 1)),
                "_ThreadCurrent" => Some(("vm_thread_current", 0)),
                "_ThreadYield" => Some(("vm_thread_yield", 0)),
                "_ThreadPark" => Some(("vm_thread_park", 0)),
                "_ThreadParkForMillis:" => {
                    Some(("vm_thread_park_for_millis", 1))
                }
                "_ThreadUnpark:" => Some(("vm_thread_unpark", 1)),
                "_Millis" => Some(("vm_millis", 0)),
                "_UnixTime" => Some(("vm_unix_time", 0)),
                _ => None,
            };
            let Some((prim_name, arity)) = expect else {
                continue;
            };

            let method_obj: &SlotObject = unsafe { slot.value.as_ref() };
            let method_map: &Map = unsafe { method_obj.map.as_ref() };
            assert!(method_map.has_code());
            assert!(method_map.is_primitive());
            let idx = unsafe { method_map.code.to_i64() } as usize;
            let prim = vm.primitives.get(idx).expect("primitive index");
            assert_eq!(prim.name, prim_name);
            assert_eq!(prim.arity, arity);

            match slot_name {
                "_SpawnPlatform:" => saw_spawn = true,
                "_ThreadJoin:" => saw_join = true,
                "_ThreadCurrent" => saw_current = true,
                "_ThreadYield" => saw_yield = true,
                "_ThreadPark" => saw_park = true,
                "_ThreadParkForMillis:" => saw_park_for = true,
                "_ThreadUnpark:" => saw_unpark = true,
                "_Millis" => saw_millis = true,
                "_UnixTime" => saw_unix_time = true,
                _ => {}
            }
        }

        assert!(saw_spawn, "_SpawnPlatform: slot not found");
        assert!(saw_join, "_ThreadJoin: slot not found");
        assert!(saw_current, "_ThreadCurrent slot not found");
        assert!(saw_yield, "_ThreadYield slot not found");
        assert!(saw_park, "_ThreadPark slot not found");
        assert!(saw_park_for, "_ThreadParkForMillis: slot not found");
        assert!(saw_unpark, "_ThreadUnpark: slot not found");
        assert!(saw_millis, "_Millis slot not found");
        assert!(saw_unix_time, "_UnixTime slot not found");
    }

    #[test]
    fn vm_has_monitor_primitives() {
        let vm = bootstrap(test_settings());
        let vm_value = lookup_dictionary_value(&vm, "VM").expect("VM missing");
        let vm_obj: &SlotObject = unsafe { vm_value.as_ref() };
        let map: &Map = unsafe { vm_obj.map.as_ref() };

        let mut saw_enter = false;
        let mut saw_exit = false;
        let mut saw_wait = false;
        let mut saw_notify = false;
        let mut saw_notify_all = false;

        for slot in unsafe { map.slots() } {
            let name: &VMString = unsafe { slot.name.as_ref() };
            match unsafe { name.as_str() } {
                "_MonitorEnter:" => saw_enter = true,
                "_MonitorExit:" => saw_exit = true,
                "_MonitorWait:" => saw_wait = true,
                "_MonitorNotify:" => saw_notify = true,
                "_MonitorNotifyAll:" => saw_notify_all = true,
                _ => {}
            }
        }

        assert!(saw_enter, "_MonitorEnter: slot not found");
        assert!(saw_exit, "_MonitorExit: slot not found");
        assert!(saw_wait, "_MonitorWait: slot not found");
        assert!(saw_notify, "_MonitorNotify: slot not found");
        assert!(saw_notify_all, "_MonitorNotifyAll: slot not found");
    }

    #[test]
    fn mirror_global_has_primitive_slots() {
        let vm = bootstrap(test_settings());
        let mirror_value =
            lookup_dictionary_value(&vm, "Mirror").expect("Mirror missing");
        let mirror_obj: &SlotObject = unsafe { mirror_value.as_ref() };
        let map: &Map = unsafe { mirror_obj.map.as_ref() };

        let mut saw_slot_count = false;
        let mut saw_at = false;
        for slot in unsafe { map.slots() } {
            let name: &VMString = unsafe { slot.name.as_ref() };
            match unsafe { name.as_str() } {
                "_MirrorSlotCount" => saw_slot_count = true,
                "_MirrorAt:" => saw_at = true,
                _ => {}
            }
        }

        assert!(saw_slot_count, "_MirrorSlotCount slot not found");
        assert!(saw_at, "_MirrorAt: slot not found");
    }

    #[test]
    fn dictionary_fixnum_matches_traits() {
        let vm = bootstrap(test_settings());
        let fixnum_value =
            lookup_dictionary_value(&vm, "Fixnum").expect("Fixnum missing");
        assert_eq!(fixnum_value.raw(), vm.special.fixnum_traits.raw());
    }

    #[test]
    fn dictionary_alien_matches_traits() {
        let vm = bootstrap(test_settings());
        let alien_value =
            lookup_dictionary_value(&vm, "Alien").expect("Alien missing");
        assert_eq!(alien_value.raw(), vm.special.alien_traits.raw());
    }

    #[test]
    fn object_pin_primitive_slot() {
        let vm = bootstrap(test_settings());
        let object_value =
            lookup_dictionary_value(&vm, "Object").expect("Object missing");
        let object_obj: &SlotObject = unsafe { object_value.as_ref() };
        let map: &Map = unsafe { object_obj.map.as_ref() };
        let mut found = false;
        for slot in unsafe { map.slots() } {
            let name: &VMString = unsafe { slot.name.as_ref() };
            if unsafe { name.as_str() } != "_Pin:" {
                continue;
            }
            found = true;
            let method_obj: &SlotObject = unsafe { slot.value.as_ref() };
            let method_map: &Map = unsafe { method_obj.map.as_ref() };
            assert!(method_map.has_code());
            assert!(method_map.is_primitive());
            let idx = unsafe { method_map.code.to_i64() } as usize;
            let prim = vm.primitives.get(idx).expect("primitive index");
            assert_eq!(prim.name, "object_pin");
            assert_eq!(prim.arity, 1);
        }
        assert!(found, "_Pin: slot not found");
    }

    #[test]
    fn object_pin_and_unpin_behaves() {
        let (vm, pinned) =
            run_source_with_vm("o = { }. Object _Pin: o. Object _IsPinned: o")
                .expect("interpret error");
        assert_eq!(pinned.raw(), vm.special.true_obj.raw());

        let (vm2, unpinned) = run_source_with_vm(
            "o = { }. Object _Pin: o. Object _Unpin: o. Object _IsPinned: o",
        )
        .expect("interpret error");
        assert_eq!(unpinned.raw(), vm2.special.false_obj.raw());
    }

    #[test]
    fn object_pin_rejects_fixnum() {
        let err = run_source("Object _Pin: 1").expect_err("expected error");
        assert!(matches!(err.error, RuntimeError::TypeError { .. }));
    }

    #[test]
    fn mirror_slot_count_and_name_at() {
        let value = run_source(
            "o = { x = 1. y := 2 }. m := Object _Reflect: o. n0 := m _MirrorSlotNameAt: 0. n1 := m _MirrorSlotNameAt: 1. (n0 _SymbolLength) _FixnumAdd: (n1 _SymbolLength)",
        )
        .expect("interpret error");
        assert!(value.is_fixnum());
        assert_eq!(unsafe { value.to_i64() }, 2);
    }

    #[test]
    fn mirror_at_put_updates_assignable_slot() {
        let value = run_source(
            "o = { x := 1 }. m := Object _Reflect: o. m _MirrorAt: \"x\" Put: 41. m _MirrorAt: \"x\"",
        )
        .expect("interpret error");
        assert!(value.is_fixnum());
        assert_eq!(unsafe { value.to_i64() }, 41);
    }

    #[test]
    fn mirror_add_and_remove_constant_slot() {
        let value = run_source(
            "o = { }. m := Object _Reflect: o. m _MirrorAddSlot: \"x\" Value: 7. v := m _MirrorAt: \"x\". m _MirrorRemoveSlot: \"x\". v",
        )
        .expect("interpret error");
        assert!(value.is_fixnum());
        assert_eq!(unsafe { value.to_i64() }, 7);
    }

    #[test]
    fn become_with_swaps_references() {
        let (_vm, value) = run_source_with_vm(
            "a = { tag = \"A\" }. b = { tag = \"B\" }. o = { ref := None }. o ref: a. Object _Become: a With: b. (o ref) tag",
        )
        .expect("interpret error");
        let s: &VMString = unsafe { value.as_ref() };
        assert_eq!(unsafe { s.as_str() }, "B");
    }

    #[test]
    fn ctype_build_struct_computes_c_layout_and_offsets() {
        let (vm, info) = run_source_with_vm(
            "CType := { parent* = Object. scalarTag: tag Size: s Align: a = { { parent* = self. impl = tag. size = s. align = a } } }. CUInt8 := CType scalarTag: 3 Size: 1 Align: 1. CUInt32 := CType scalarTag: 7 Size: 4 Align: 4. CTiny := CType _CTypeBuildStruct: { a = CUInt8. b = CUInt32. c = CUInt8 }. CTiny _CTypeFieldInfoAt: \"b\"",
        )
        .expect("interpret error");

        let info_obj: &SlotObject = unsafe { info.as_ref() };
        let info_map: &Map = unsafe { info_obj.map.as_ref() };
        let mut offset = None;
        for slot in unsafe { info_map.slots() } {
            let name: &VMString = unsafe { slot.name.as_ref() };
            if unsafe { name.as_str() } == "offset" {
                offset = Some(slot.value);
            }
        }
        assert_eq!(unsafe { offset.expect("offset slot").to_i64() }, 4);

        let c_tiny =
            lookup_dictionary_value(&vm, "CTiny").expect("CTiny missing");
        let c_tiny_obj: &SlotObject = unsafe { c_tiny.as_ref() };
        let c_tiny_map: &Map = unsafe { c_tiny_obj.map.as_ref() };
        let mut size = None;
        let mut align = None;
        for slot in unsafe { c_tiny_map.slots() } {
            let name: &VMString = unsafe { slot.name.as_ref() };
            match unsafe { name.as_str() } {
                "size" => size = Some(slot.value),
                "align" => align = Some(slot.value),
                _ => {}
            }
        }
        assert_eq!(unsafe { size.expect("size slot").to_i64() }, 12);
        assert_eq!(unsafe { align.expect("align slot").to_i64() }, 4);
    }

    #[test]
    fn ctype_build_struct_rejects_non_ctype_field() {
        let err = run_source(
            "CType := { parent* = Object. scalarTag: tag Size: s Align: a = { { parent* = self. impl = tag. size = s. align = a } } }. CType _CTypeBuildStruct: { nope = { x = 1 } }",
        )
        .expect_err("expected error");
        assert!(matches!(err.error, RuntimeError::Unimplemented { .. }));
    }

    #[test]
    fn ctype_field_info_returns_member_descriptor() {
        let value = run_source(
            "CType := { parent* = Object. scalarTag: tag Size: s Align: a = { { parent* = self. impl = tag. size = s. align = a } } }. CUInt8 := CType scalarTag: 3 Size: 1 Align: 1. CUInt32 := CType scalarTag: 7 Size: 4 Align: 4. CTiny := CType _CTypeBuildStruct: { a = CUInt8. b = CUInt32. c = CUInt8 }. infoA := CTiny _CTypeFieldInfoAt: \"a\". infoB := CTiny _CTypeFieldInfoAt: \"b\". ((infoA type) _CTypeScalarTag) _FixnumAdd: ((infoB type) _CTypeScalarTag)",
        )
        .expect("interpret error");
        assert!(value.is_fixnum());
        assert_eq!(unsafe { value.to_i64() }, 10);
    }

    #[test]
    fn proxy_generic_field_access_uses_ctype_layout() {
        let value = run_source(
            "Object _Extend: True With: { ifTrue: t IfFalse: f = { t call } }. Object _Extend: False With: { ifTrue: t IfFalse: f = { f call } }. CType := { parent* = Object. scalarTag: tag Size: s Align: a = { { parent* = self. impl = tag. size = s. align = a } }. struct: d = { self _CTypeBuildStruct: d } }. CUInt8 := CType scalarTag: 3 Size: 1 Align: 1. CUInt32 := CType scalarTag: 7 Size: 4 Align: 4. CTiny := CType struct: { a = CUInt8. b = CUInt32. c = CUInt8 }. Proxy := { parent* = Object. fromCType: t = { { parent* = Proxy. ctype = t. backing = ByteArray _CloneWithSize: (t size) } }. u8At: i = { (self backing) _ByteArrayU8At: i }. u32At: i = { (self backing) _ByteArrayU32At: i }. u8At: i Put: v = { (self backing) _ByteArrayU8At: i Put: v }. u32At: i Put: v = { (self backing) _ByteArrayU32At: i Put: v }. readCType: t At: offset = { ((t _CTypeScalarTag) _FixnumEq: 3) ifTrue: [ self u8At: offset ] IfFalse: [ self u32At: offset ] }. writeCType: t At: offset Value: value = { ((t _CTypeScalarTag) _FixnumEq: 3) ifTrue: [ self u8At: offset Put: value ] IfFalse: [ self u32At: offset Put: value ] }. atField: name = { info := (self ctype) _CTypeFieldInfoAt: name. self readCType: (info type) At: (info offset) }. atField: name Put: value = { info := (self ctype) _CTypeFieldInfoAt: name. self writeCType: (info type) At: (info offset) Value: value. value } }. p := Proxy fromCType: CTiny. p atField: \"a\" Put: 7. p atField: \"b\" Put: 1234. p atField: \"c\" Put: 9. ((p atField: \"a\") _FixnumAdd: (p atField: \"b\")) _FixnumAdd: (p atField: \"c\")",
        )
        .expect("interpret error");
        assert!(value.is_fixnum());
        assert_eq!(unsafe { value.to_i64() }, 1250);
    }

    #[test]
    fn ctype_size_align_metadata() {
        let csize_align = run_source(
            "CSize := { impl := 13. size = 8. align = 8 }. CSize align",
        )
        .expect("interpret error");
        assert!(csize_align.is_fixnum());
        assert_eq!(unsafe { csize_align.to_i64() }, 8);
    }

    #[test]
    fn ctype_struct_descriptor_has_required_slots() {
        let (vm, _) = run_source_with_vm(
            "CInt32 := { impl := 6. size = 4. align = 4 }. CPair := { impl := None. size = 8. align = 4. first = CInt32. second = CInt32 }. None",
        )
        .expect("interpret error");
        let cpair =
            lookup_dictionary_value(&vm, "CPair").expect("CPair missing");
        let obj: &object::SlotObject = unsafe { cpair.as_ref() };
        let map: &Map = unsafe { obj.map.as_ref() };
        let mut names = Vec::new();
        for slot in unsafe { map.slots() } {
            let name: &VMString = unsafe { slot.name.as_ref() };
            names.push(unsafe { name.as_str() }.to_string());
        }
        assert!(names.iter().any(|n| n == "impl"));
        assert!(names.iter().any(|n| n == "size"));
        assert!(names.iter().any(|n| n == "align"));
    }

    #[test]
    fn ctype_struct_descriptor_roundtrip_through_array() {
        let value = run_source(
            "cint := { impl := 6. size = 4. align = 4 }. cpair := { impl := None. size = 8. align = 4. first := None. second := None }. cpair first: cint. cpair second: cint. ts := Array _ArrayCloneWithSize: 1. ts _ArrayAt: 0 Put: cpair. (ts _ArrayAt: 0) size",
        )
        .expect("interpret error");
        assert!(value.is_fixnum());
        assert_eq!(unsafe { value.to_i64() }, 8);
    }

    #[test]
    fn alien_u64_roundtrip_with_bignum() {
        let (vm, value) = run_source_with_vm(
            "max := (4611686018427387903 _FixnumToBignum). big := max _BignumAdd: max. a := Alien _AlienNew: 8. a _AlienU64At: 0 Put: big. (a _AlienU64At: 0) _BignumEq: big",
        )
        .expect("interpret error");
        assert_eq!(value.raw(), vm.special.true_obj.raw());
    }

    #[test]
    fn alien_dynamic_call_strlen() {
        let value = run_source(
            "CPointer := { impl := 12. size = 8. align = 8 }. CSize := { impl := 13. size = 8. align = 8 }. lib := Alien _LibraryOpen: \"libc.so.6\". fn := lib _LibrarySym: \"strlen\". s := \"hello\" _StringToByteArray. n := \"hello\" _StringLength. bytes := n _FixnumAdd: 1. a := Alien _AlienNew: bytes. a _AlienCopyFrom: s Offset: 0 Length: bytes. ts := Array _ArrayCloneWithSize: 1. ts _ArrayAt: 0 Put: CPointer. av := Array _ArrayCloneWithSize: 1. av _ArrayAt: 0 Put: a. r := fn _AlienCallWithTypes: ts Args: av ReturnType: CSize. lib _LibraryClose. a _AlienFree. r",
        )
        .expect("interpret error");
        assert!(value.is_fixnum());
        assert_eq!(unsafe { value.to_i64() }, 5);
    }

    #[test]
    fn alien_dynamic_call_length_mismatch_is_error() {
        let err = run_source(
            "CPointer := { impl := 12. size = 8. align = 8 }. CSize := { impl := 13. size = 8. align = 8 }. lib := Alien _LibraryOpen: \"libc.so.6\". fn := lib _LibrarySym: \"strlen\". ts := Array _ArrayCloneWithSize: 1. ts _ArrayAt: 0 Put: CPointer. av := Array _ArrayCloneWithSize: 0. fn _AlienCallWithTypes: ts Args: av ReturnType: CSize",
        )
        .expect_err("expected error");
        assert!(matches!(
            err.error,
            RuntimeError::Unimplemented {
                message: "parameter types and argument values length mismatch"
            }
        ));
    }

    #[test]
    fn alien_dynamic_call_struct_by_value_arg() {
        let addr = ffi_sum_pair as *const () as usize;
        let src = format!(
            "cint := {{ impl := 6. size = 4. align = 4 }}. cpair := {{ impl := None. size = 8. align = 4. first := None. second := None }}. cpair first: cint. cpair second: cint. fn := Alien _AlienFromAddress: {addr} Size: 0. pair := ByteArray _CloneWithSize: 8. pair _ByteArrayI32At: 0 Put: 40. pair _ByteArrayI32At: 4 Put: 2. ts := Array _ArrayCloneWithSize: 1. ts _ArrayAt: 0 Put: cpair. av := Array _ArrayCloneWithSize: 1. av _ArrayAt: 0 Put: pair. fn _AlienCallWithTypes: ts Args: av ReturnType: cint"
        );
        let value = run_source(&src).expect("interpret error");
        assert!(value.is_fixnum());
        assert_eq!(unsafe { value.to_i64() }, 42);
    }

    #[test]
    fn alien_dynamic_call_struct_by_value_return() {
        let addr = ffi_make_pair as *const () as usize;
        let src = format!(
            "cint := {{ impl := 6. size = 4. align = 4 }}. cpair := {{ impl := None. size = 8. align = 4. first := None. second := None }}. cpair first: cint. cpair second: cint. fn := Alien _AlienFromAddress: {addr} Size: 0. ts := Array _ArrayCloneWithSize: 2. ts _ArrayAt: 0 Put: cint. ts _ArrayAt: 1 Put: cint. av := Array _ArrayCloneWithSize: 2. av _ArrayAt: 0 Put: 7. av _ArrayAt: 1 Put: 35. out := fn _AlienCallWithTypes: ts Args: av ReturnType: cpair. (out _ByteArrayI32At: 0) _FixnumAdd: (out _ByteArrayI32At: 4)"
        );
        let value = run_source(&src).expect("interpret error");
        assert!(value.is_fixnum());
        assert_eq!(unsafe { value.to_i64() }, 42);
    }

    #[test]
    fn ffi_proxy_argument_lowering_in_user_space() {
        let value = run_source(
            "Object _Extend: Object With: { cArgValue = { self } }. Object _Extend: Alien With: { callWithOneType: t Arg: v ReturnType: r = { ts := Array _ArrayCloneWithSize: 1. ts _ArrayAt: 0 Put: t. av := Array _ArrayCloneWithSize: 1. av _ArrayAt: 0 Put: (v cArgValue). self _AlienCallWithTypes: ts Args: av ReturnType: r } }. CPointer := { impl := 12. size = 8. align = 8 }. CSize := { impl := 13. size = 8. align = 8 }. lib := Alien _LibraryOpen: \"libc.so.6\". fn := lib _LibrarySym: \"strlen\". p := { backing = \"hello\". cArgValue = { self backing } }. r := fn callWithOneType: CPointer Arg: p ReturnType: CSize. lib _LibraryClose. r",
        )
        .expect("interpret error");
        assert!(value.is_fixnum());
        assert_eq!(unsafe { value.to_i64() }, 5);
    }

    #[test]
    fn proxy_works_with_bytearray_backing() {
        let value = run_source(
            "Object _Extend: ByteArray With: { u64At: i = { self _ByteArrayU64At: i }. u64At: i Put: v = { self _ByteArrayU64At: i Put: v } }. Proxy := { readAfterWrite: backing = { backing u64At: 0 Put: 42. backing u64At: 0 } }. b := ByteArray _CloneWithSize: 8. Proxy readAfterWrite: b",
        )
        .expect("interpret error");
        assert!(value.is_fixnum());
        assert_eq!(unsafe { value.to_i64() }, 42);
    }

    #[test]
    fn proxy_works_with_alien_backing() {
        let value = run_source(
            "Object _Extend: Alien With: { u64At: i = { self _AlienU64At: i }. u64At: i Put: v = { self _AlienU64At: i Put: v }. free = { self _AlienFree } }. Proxy := { readAfterWrite: backing = { backing u64At: 0 Put: 123. backing u64At: 0 } }. a := Alien _AlienNew: 8. v := Proxy readAfterWrite: a. a free. v",
        )
        .expect("interpret error");
        assert!(value.is_fixnum());
        assert_eq!(unsafe { value.to_i64() }, 123);
    }

    #[test]
    fn proxy_pin_wrapper_behaves() {
        let (vm, value) = run_source_with_vm(
            "Proxy := { fromBacking: b = { { backing := b. pin = { Object _Pin: (self backing). self }. unpin = { Object _Unpin: (self backing). self }. isPinned = { Object _IsPinned: (self backing) } } } }. p := Proxy fromBacking: { }. p pin. a := p isPinned. p unpin. b := p isPinned. a",
        )
        .expect("interpret error");
        assert_eq!(value.raw(), vm.special.true_obj.raw());
    }

    #[test]
    fn extend_with_adds_constant_slots() {
        let value =
            run_source("o = { }. Object _Extend: o With: { x = 7 }. o x")
                .expect("interpret error");
        assert!(value.is_fixnum());
        assert_eq!(unsafe { value.to_i64() }, 7);
    }

    #[test]
    fn extend_with_rejects_assignable_slots() {
        let err = run_source("o = { }. Object _Extend: o With: { x := 7 }")
            .expect_err("expected error");
        match err.error {
            RuntimeError::Unimplemented { .. } => {}
            other => panic!("expected Unimplemented, got {other:?}"),
        }
    }

    #[test]
    fn extend_with_rejects_code() {
        let err = run_source("o = { }. Object _Extend: o With: { x = 1. 2 }")
            .expect_err("expected error");
        assert!(matches!(err.error, RuntimeError::Unimplemented { .. }));
    }

    // ── Source map / error location tests ────────────────────────

    #[test]
    fn error_has_source_location() {
        let err = run_source("5 foo").expect_err("expected error");
        assert!(matches!(
            err.error,
            RuntimeError::MessageNotUnderstood { .. }
        ));
        let loc = err.location.expect("error should have source location");
        // "5 foo" — the send expression spans the whole thing
        assert_eq!(loc.start, 0);
        assert_eq!(loc.end, 5);
    }

    #[test]
    fn error_location_points_to_failing_send() {
        // "x = 5. x bar" — the error is on "x bar" (offset 7..12)
        let err = run_source("x = 5. x bar").expect_err("expected error");
        let loc = err.location.expect("error should have source location");
        assert_eq!(loc.start, 7);
        assert_eq!(loc.end, 12);
    }

    #[test]
    fn error_location_binary_message() {
        // "42 + True" — fixnum + fails on dispatching +
        let err = run_source("42 + True").expect_err("expected error");
        let loc = err.location.expect("error should have source location");
        // The whole binary expression "42 + True"
        assert_eq!(loc.start, 0);
        assert_eq!(loc.end, 9);
    }

    #[test]
    fn error_location_keyword_message() {
        let err = run_source("42 foo: 1 Bar: 2").expect_err("expected error");
        let loc = err.location.expect("error should have source location");
        assert_eq!(loc.start, 0);
        assert_eq!(loc.end, 16);
    }

    #[test]
    fn compile_error_location_undefined_global() {
        let (arena, exprs) = parse_source("NoSuchGlobal");
        let mut vm = bootstrap(test_settings());
        vm.open_module(USER_MODULE);
        let err = Compiler::compile_for_vm_ids(&vm, &arena, &exprs)
            .expect_err("expected error");
        let span = err.span.expect("error should have source span");
        assert_eq!(span.start.offset, 0);
        assert_eq!(span.end.offset, 12);
    }

    #[test]
    fn error_location_multiline() {
        let src = "x = 5.\ny = 10.\nx blah";
        let err = run_source(src).expect_err("expected error");
        let loc = err.location.expect("error should have source location");
        // "x blah" starts at offset 15
        assert_eq!(loc.start, 15);
        assert_eq!(loc.end, 21);
    }

    #[test]
    fn successful_execution_no_error() {
        // Ensure source maps don't break normal execution
        let value = run_source("42").expect("interpret error");
        assert!(value.is_fixnum());
        assert_eq!(unsafe { value.to_i64() }, 42);
    }
}
