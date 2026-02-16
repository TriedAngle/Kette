use std::alloc::Layout;
use std::collections::HashMap;
use std::mem::size_of;
use std::ptr;

use bytecode::{Instruction, Op};
use heap::{HeapProxy, RootProvider};
use object::{
    init_array, slot_object_allocation_size, Array, Block, Code, Header, Map,
    ObjectType, Slot, SlotObject, VMString, Value,
};

use crate::VM;

const MAX_FRAMES: usize = 1024;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RuntimeError {
    MessageNotUnderstood { receiver: Value, message: Value },
    NonLocalReturnExpired,
    StackOverflow,
    TypeError { expected: &'static str, got: Value },
    Unimplemented { message: &'static str },
    UndefinedGlobal { name: String },
}

#[derive(Debug, Clone)]
struct Frame {
    code: Value,
    pc: usize,
    registers: Vec<Value>,
    temp_array: Value,
    is_block: bool,
    method_frame_idx: usize,
    holder: Value,
    holder_slot_index: u32,
}

pub struct InterpreterState {
    acc: Value,
    frames: Vec<Frame>,
}

pub(crate) struct InterpreterRoots<'a> {
    acc: &'a mut Value,
    frames: &'a mut [Frame],
    special: &'a mut object::SpecialObjects,
    intern_table: &'a mut HashMap<String, Value>,
    assoc_map: &'a mut Value,
    dictionary: &'a mut Value,
    pub(crate) scratch: &'a mut Vec<Value>,
}

impl RootProvider for InterpreterRoots<'_> {
    fn visit_roots(&mut self, visitor: &mut dyn FnMut(&mut Value)) {
        visitor(self.acc);
        for frame in self.frames.iter_mut() {
            visitor(&mut frame.code);
            visitor(&mut frame.temp_array);
            visitor(&mut frame.holder);
            for reg in frame.registers.iter_mut() {
                visitor(reg);
            }
        }
        visitor(&mut self.special.nil);
        visitor(&mut self.special.true_obj);
        visitor(&mut self.special.false_obj);
        visitor(&mut self.special.map_map);
        visitor(&mut self.special.array_traits);
        visitor(&mut self.special.bytearray_traits);
        visitor(&mut self.special.bignum_traits);
        visitor(&mut self.special.alien_traits);
        visitor(&mut self.special.string_traits);
        visitor(&mut self.special.ratio_traits);
        visitor(&mut self.special.fixnum_traits);
        visitor(&mut self.special.code_traits);
        visitor(&mut self.special.float_traits);
        visitor(self.assoc_map);
        visitor(self.dictionary);
        for v in self.intern_table.values_mut() {
            visitor(v);
        }
        for v in self.scratch.iter_mut() {
            visitor(v);
        }
    }
}

pub fn interpret(vm: &mut VM, code: Value) -> Result<Value, RuntimeError> {
    interpret_with_receiver(vm, code, vm.special.nil)
}

pub fn interpret_with_receiver(
    vm: &mut VM,
    code: Value,
    receiver: Value,
) -> Result<Value, RuntimeError> {
    let mut state = InterpreterState {
        acc: vm.special.nil,
        frames: Vec::new(),
    };

    push_entry_frame(vm, &mut state, code, receiver)?;
    run(vm, &mut state)
}

fn run(
    vm: &mut VM,
    state: &mut InterpreterState,
) -> Result<Value, RuntimeError> {
    while let Some(frame_idx) = current_frame_index(state) {
        let (instr, code_val) = {
            let frame = &mut state.frames[frame_idx];
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
                let frame = &state.frames[frame_idx];
                state.acc = get_register(frame, reg)?;
            }
            Instruction::StoreLocal { reg } => {
                let value = state.acc;
                let frame = &mut state.frames[frame_idx];
                set_register(frame, reg, value)?;
            }
            Instruction::Mov { dst, src } => {
                let value = {
                    let frame = &state.frames[frame_idx];
                    get_register(frame, src)?
                };
                let frame = &mut state.frames[frame_idx];
                set_register(frame, dst, value)?;
            }
            Instruction::LoadStack { offset } => {
                let nil = vm.special.nil;
                let frame = &mut state.frames[frame_idx];
                state.acc = load_stack_slot(frame, offset, nil);
            }
            Instruction::StoreStack { offset } => {
                let value = state.acc;
                let nil = vm.special.nil;
                let frame = &mut state.frames[frame_idx];
                store_stack_slot(frame, offset, value, nil);
            }
            Instruction::MovToStack { offset, src } => {
                let value = {
                    let frame = &state.frames[frame_idx];
                    get_register(frame, src)?
                };
                let nil = vm.special.nil;
                let frame = &mut state.frames[frame_idx];
                store_stack_slot(frame, offset, value, nil);
            }
            Instruction::MovFromStack { dst, offset } => {
                let nil = vm.special.nil;
                let value = {
                    let frame = &mut state.frames[frame_idx];
                    load_stack_slot(frame, offset, nil)
                };
                let frame = &mut state.frames[frame_idx];
                set_register(frame, dst, value)?;
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
                let value = {
                    let frame = &state.frames[frame_idx];
                    get_register(frame, src)?
                };
                store_temp(vm, state, frame_idx, array_idx, idx, value)?;
            }
            Instruction::MovFromTemp {
                dst,
                array_idx,
                idx,
            } => {
                let value = load_temp(vm, state, frame_idx, array_idx, idx)?;
                let frame = &mut state.frames[frame_idx];
                set_register(frame, dst, value)?;
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
                let value = {
                    let frame = &state.frames[frame_idx];
                    get_register(frame, src)?
                };
                store_assoc(vm, code_val, idx, value)?;
            }
            Instruction::MovFromAssoc { dst, idx } => {
                let value = load_assoc(vm, code_val, idx)?;
                let frame = &mut state.frames[frame_idx];
                set_register(frame, dst, value)?;
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
                ..
            } => {
                dispatch_send(
                    vm,
                    state,
                    frame_idx,
                    code_val,
                    message_idx,
                    reg,
                    argc,
                )?;
            }
            Instruction::Resend {
                message_idx,
                reg,
                argc,
                ..
            } => {
                dispatch_resend(
                    vm,
                    state,
                    frame_idx,
                    code_val,
                    message_idx,
                    reg,
                    argc,
                    None,
                )?;
            }
            Instruction::DirectedResend {
                message_idx,
                reg,
                argc,
                delegate_idx,
                ..
            } => {
                dispatch_resend(
                    vm,
                    state,
                    frame_idx,
                    code_val,
                    message_idx,
                    reg,
                    argc,
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
                state.frames.pop();
                if state.frames.is_empty() {
                    return Ok(state.acc);
                }
            }
            Instruction::Return => {
                let method_idx = state.frames[frame_idx].method_frame_idx;
                if method_idx >= state.frames.len() {
                    return Err(RuntimeError::NonLocalReturnExpired);
                }
                state.frames.truncate(method_idx);
                if state.frames.is_empty() {
                    return Ok(state.acc);
                }
            }
        }
    }

    Ok(state.acc)
}

fn push_entry_frame(
    vm: &mut VM,
    state: &mut InterpreterState,
    code: Value,
    receiver: Value,
) -> Result<(), RuntimeError> {
    push_method_frame(vm, state, code, receiver, None, vm.special.nil, 0)
}

fn push_method_frame(
    vm: &mut VM,
    state: &mut InterpreterState,
    code_val: Value,
    receiver: Value,
    args_source: Option<(usize, u16, u8)>,
    holder: Value,
    holder_slot_index: u32,
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
    let nil = vm.special.nil;
    let mut registers = vec![nil; reg_count.max(1)];
    registers[0] = receiver;

    let temp_array = if code.temp_count() > 0 {
        state.acc = receiver;
        alloc_temp_array(vm, state, code.temp_count())?
    } else {
        nil
    };

    if let Some((src_idx, reg, argc)) = args_source {
        copy_args_from_frame(state, src_idx, reg, argc, &mut registers)?;
    }

    let method_frame_idx = state.frames.len();
    state.frames.push(Frame {
        code: code_val,
        pc: 0,
        registers,
        temp_array,
        is_block: false,
        method_frame_idx,
        holder,
        holder_slot_index,
    });

    Ok(())
}

fn push_block_frame(
    vm: &mut VM,
    state: &mut InterpreterState,
    code_val: Value,
    receiver: Value,
    args_source: (usize, u16, u8),
) -> Result<(), RuntimeError> {
    if state.frames.len() >= MAX_FRAMES {
        return Err(RuntimeError::StackOverflow);
    }

    let code = unsafe { &*expect_code(code_val)? };
    let arg_count = code.arg_count() as usize;
    let provided = args_source.2 as usize;
    if provided != arg_count {
        return Err(RuntimeError::TypeError {
            expected: "argument count",
            got: Value::from_i64(provided as i64),
        });
    }

    let reg_count = code.register_count() as usize;
    let nil = vm.special.nil;
    let mut registers = vec![nil; reg_count.max(1)];
    registers[0] = receiver;
    copy_args_from_frame(
        state,
        args_source.0,
        args_source.1,
        args_source.2,
        &mut registers,
    )?;

    let method_frame_idx = find_enclosing_method_idx(&state.frames)
        .unwrap_or_else(|| state.frames.len().saturating_sub(1));
    let temp_array =
        find_enclosing_temp_array(vm, &state.frames).unwrap_or(nil);
    let (holder, holder_slot_index) = find_enclosing_holder(vm, &state.frames);

    state.frames.push(Frame {
        code: code_val,
        pc: 0,
        registers,
        temp_array,
        is_block: true,
        method_frame_idx,
        holder,
        holder_slot_index,
    });

    Ok(())
}

fn push_block_frame_with_args(
    vm: &mut VM,
    state: &mut InterpreterState,
    code_val: Value,
    receiver: Value,
    args: &[Value],
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
    let nil = vm.special.nil;
    let mut registers = vec![nil; reg_count.max(1)];
    registers[0] = receiver;
    for (i, arg) in args.iter().enumerate() {
        let idx = i + 1;
        if idx < registers.len() {
            registers[idx] = *arg;
        }
    }

    let parent_temp =
        find_enclosing_temp_array(vm, &state.frames).unwrap_or(nil);
    let temp_array = if code.temp_count() > 0 {
        state.acc = receiver;
        alloc_temp_array(vm, state, code.temp_count())?
    } else {
        parent_temp
    };

    let method_frame_idx = state.frames.len();
    state.frames.push(Frame {
        code: code_val,
        pc: 0,
        registers,
        temp_array,
        is_block: true,
        method_frame_idx,
        holder: vm.special.nil,
        holder_slot_index: 0,
    });

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
) -> Result<(), RuntimeError> {
    let receiver = state.acc;

    let code: &Code = unsafe { code_val.as_ref() };
    let message = unsafe { code.constant(message_idx as u32) };
    if is_block_value(receiver)? && is_block_call_selector(message, argc) {
        let block_code = block_code(receiver, vm.special.nil)?;
        let receiver_self = state.frames[frame_idx].registers[0];
        return push_block_frame(
            vm,
            state,
            block_code,
            receiver_self,
            (frame_idx, reg, argc),
        );
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
            ..
        } => dispatch_slot(
            vm, state, frame_idx, receiver, holder, slot, slot_index, reg, argc,
        ),
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
    let block_code = block_code(receiver, vm.special.nil)?;
    let frame_idx = state.frames.len() - 1;
    let receiver_self = state.frames[frame_idx].registers[0];
    push_block_frame_with_args(vm, state, block_code, receiver_self, args)?;
    Ok(state.acc)
}

fn is_block_call_selector(message: Value, argc: u8) -> bool {
    let name = match message_name(message) {
        Some(name) => name,
        None => return false,
    };
    if argc == 0 {
        return name == "call";
    }
    if argc > 8 {
        return false;
    }
    let expected = block_call_selector(argc as usize);
    name == expected
}

fn message_name(message: Value) -> Option<String> {
    if !message.is_ref() {
        return None;
    }
    let header: &Header = unsafe { message.as_ref() };
    if header.object_type() != ObjectType::Str {
        return None;
    }
    let s: &VMString = unsafe { message.as_ref() };
    Some(unsafe { s.as_str() }.to_string())
}

fn block_call_selector(argc: usize) -> String {
    if argc == 0 {
        return "call".to_string();
    }
    let mut out = String::from("call:");
    for _ in 1..argc {
        out.push_str("With:");
    }
    out
}

fn dispatch_resend(
    vm: &mut VM,
    state: &mut InterpreterState,
    frame_idx: usize,
    code_val: Value,
    message_idx: u16,
    reg: u16,
    argc: u8,
    delegate_idx: Option<u16>,
) -> Result<(), RuntimeError> {
    let receiver = state.frames[frame_idx].registers[0];
    let holder = state.frames[frame_idx].holder;

    let code: &Code = unsafe { code_val.as_ref() };
    let message = unsafe { code.constant(message_idx as u32) };
    let delegate_name =
        delegate_idx.map(|idx| unsafe { code.constant(idx as u32) });

    let result = lookup_resend(holder, message, delegate_name, &vm.special)?;
    match result {
        object::LookupResult::None => {
            Err(RuntimeError::MessageNotUnderstood { receiver, message })
        }
        object::LookupResult::Found {
            holder,
            slot,
            slot_index,
            ..
        } => dispatch_slot(
            vm, state, frame_idx, receiver, holder, slot, slot_index, reg, argc,
        ),
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
        let value = get_register(&state.frames[frame_idx], reg)?;
        write_holder_value(vm, holder, slot.value, value)?;
        state.acc = value;
        return Ok(());
    }

    if slot.is_assignable() {
        state.acc = slot.value;
        return Ok(());
    }

    if let Some(target) = extract_method_target(slot.value, vm.special.nil)? {
        match target {
            MethodTarget::Code(code_val) => {
                return push_method_frame(
                    vm,
                    state,
                    code_val,
                    receiver,
                    Some((frame_idx, reg, argc)),
                    holder,
                    slot_index,
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
                let args =
                    collect_args_from_frame(state, frame_idx, reg, argc)?;
                state.acc = (primitive.func)(vm, state, receiver, &args)?;
                return Ok(());
            }
        }
    }

    state.acc = slot.value;
    Ok(())
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
        let regs = &state.frames[frame_idx].registers;
        if values_end > regs.len() {
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
                let regs = &roots.frames[frame_idx].registers;
                let vals_dst = obj_ptr.add(1) as *mut Value;
                for i in 0..value_count {
                    *vals_dst.add(i) = regs[values_start + i];
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

    let mut scratch = vec![map_val];
    let block = with_roots(vm, state, &mut scratch, |proxy, roots| {
        let size = size_of::<Block>();
        let layout = Layout::from_size_align(size, 8).unwrap();
        let ptr = proxy.allocate(layout, roots);
        let map_val = roots.scratch[0];
        let block_ptr = ptr.as_ptr() as *mut Block;
        unsafe {
            ptr::write(
                block_ptr,
                Block {
                    header: Header::new(ObjectType::Block),
                    map: map_val,
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
) -> Result<Value, RuntimeError> {
    let mut scratch = Vec::new();
    let arr = with_roots(vm, state, &mut scratch, |proxy, roots| {
        let size = size_of::<Array>() + len as usize * size_of::<Value>();
        let layout = Layout::from_size_align(size, 8).unwrap();
        let ptr = proxy.allocate(layout, roots);
        let arr_ptr = ptr.as_ptr() as *mut Array;
        unsafe {
            init_array(arr_ptr, len as u64);
            let nil = roots.special.nil;
            let elems = arr_ptr.add(1) as *mut Value;
            for i in 0..len as usize {
                *elems.add(i) = nil;
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
    let assoc_or_name = unsafe { code.constant(idx as u32) };

    if assoc_or_name.is_ref() {
        let header: &Header = unsafe { assoc_or_name.as_ref() };
        match header.object_type() {
            ObjectType::Slots => {
                let assoc_obj = unsafe { &*expect_slot_object(assoc_or_name)? };
                return unsafe {
                    Ok(assoc_obj.read_value(SlotObject::VALUES_OFFSET))
                };
            }
            ObjectType::Str => {
                if let Some(value) = lookup_assoc_value(vm, assoc_or_name)? {
                    return Ok(value);
                }

                let name = symbol_to_string(assoc_or_name)
                    .unwrap_or_else(|| "<symbol>".to_string());
                return Err(RuntimeError::UndefinedGlobal { name });
            }
            _ => {}
        }
    }

    Err(RuntimeError::TypeError {
        expected: "assoc or symbol",
        got: assoc_or_name,
    })
}

fn lookup_assoc_value(
    vm: &VM,
    name: Value,
) -> Result<Option<Value>, RuntimeError> {
    let dict = vm.dictionary;
    unsafe {
        let dict_obj: &SlotObject = dict.as_ref();
        let map: &Map = dict_obj.map.as_ref();
        let slots = map.slots();
        for slot in slots {
            if slot.name.raw() == name.raw() {
                let assoc = slot.value;
                let assoc_obj = &*expect_slot_object(assoc)?;
                return Ok(Some(
                    assoc_obj.read_value(SlotObject::VALUES_OFFSET),
                ));
            }
        }
    }
    Ok(None)
}

fn symbol_to_string(sym: Value) -> Option<String> {
    if !sym.is_ref() {
        return None;
    }

    let header: &Header = unsafe { sym.as_ref() };
    if header.object_type() != ObjectType::Str {
        return None;
    }

    let s: &VMString = unsafe { sym.as_ref() };
    Some(unsafe { s.as_str() }.to_string())
}

fn store_assoc(
    vm: &mut VM,
    code_val: Value,
    idx: u16,
    value: Value,
) -> Result<(), RuntimeError> {
    let code: &Code = unsafe { code_val.as_ref() };
    let assoc = unsafe { code.constant(idx as u32) };
    let assoc_obj = unsafe { &mut *expect_slot_object_mut(assoc)? };
    unsafe { assoc_obj.write_value(SlotObject::VALUES_OFFSET, value) };
    if value.is_ref() {
        vm.heap_proxy.write_barrier(assoc, value);
    }
    Ok(())
}

fn load_temp(
    vm: &VM,
    state: &InterpreterState,
    frame_idx: usize,
    array_idx: u16,
    idx: u16,
) -> Result<Value, RuntimeError> {
    let array =
        get_temp_array(&state.frames[frame_idx], array_idx, vm.special.nil)?;
    let array = unsafe { &*expect_array(array)? };
    if idx as u64 >= array.len() {
        return Err(RuntimeError::TypeError {
            expected: "temp index",
            got: Value::from_i64(idx as i64),
        });
    }
    unsafe {
        let elems = (array as *const Array).add(1) as *const Value;
        Ok(*elems.add(idx as usize))
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
        get_temp_array(&state.frames[frame_idx], array_idx, vm.special.nil)?;
    let array = unsafe { &*expect_array(array_val)? };
    if idx as u64 >= array.len() {
        return Err(RuntimeError::TypeError {
            expected: "temp index",
            got: Value::from_i64(idx as i64),
        });
    }
    unsafe {
        let elems = (array as *const Array).add(1) as *mut Value;
        *elems.add(idx as usize) = value;
    }
    if value.is_ref() {
        vm.heap_proxy.write_barrier(array_val, value);
    }
    Ok(())
}

fn get_temp_array(
    frame: &Frame,
    array_idx: u16,
    nil: Value,
) -> Result<Value, RuntimeError> {
    if array_idx != 0 {
        return Err(RuntimeError::TypeError {
            expected: "temp array index",
            got: Value::from_i64(array_idx as i64),
        });
    }
    if frame.temp_array.raw() == nil.raw() {
        return Err(RuntimeError::TypeError {
            expected: "temp array",
            got: frame.temp_array,
        });
    }
    Ok(frame.temp_array)
}

fn copy_args_from_frame(
    state: &InterpreterState,
    frame_idx: usize,
    reg: u16,
    argc: u8,
    out_registers: &mut [Value],
) -> Result<(), RuntimeError> {
    let start = reg as usize;
    let end = start + argc as usize;
    let regs = &state.frames[frame_idx].registers;
    if end > regs.len() {
        return Err(RuntimeError::TypeError {
            expected: "argument register range",
            got: Value::from_i64(end as i64),
        });
    }
    for i in 0..argc as usize {
        let dst = i + 1;
        if dst >= out_registers.len() {
            return Err(RuntimeError::TypeError {
                expected: "argument register range",
                got: Value::from_i64(dst as i64),
            });
        }
        out_registers[dst] = regs[start + i];
    }
    Ok(())
}

fn collect_args_from_frame(
    state: &InterpreterState,
    frame_idx: usize,
    reg: u16,
    argc: u8,
) -> Result<Vec<Value>, RuntimeError> {
    let start = reg as usize;
    let end = start + argc as usize;
    let regs = &state.frames[frame_idx].registers;
    if end > regs.len() {
        return Err(RuntimeError::TypeError {
            expected: "argument register range",
            got: Value::from_i64(end as i64),
        });
    }
    Ok(regs[start..end].to_vec())
}

enum MethodTarget {
    Code(Value),
    Primitive(usize),
}

fn extract_method_target(
    value: Value,
    nil: Value,
) -> Result<Option<MethodTarget>, RuntimeError> {
    if !value.is_ref() {
        return Ok(None);
    }
    let header: &Header = unsafe { value.as_ref() };
    match header.object_type() {
        ObjectType::Code => Ok(Some(MethodTarget::Code(value))),
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
                if map.code.raw() == nil.raw() {
                    return Err(RuntimeError::TypeError {
                        expected: "method code",
                        got: map.code,
                    });
                }
                Ok(Some(MethodTarget::Code(map.code)))
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

fn block_code(block_val: Value, nil: Value) -> Result<Value, RuntimeError> {
    let block = unsafe { &*expect_block(block_val)? };
    let map: &Map = unsafe { block.map.as_ref() };
    if map.code.raw() == nil.raw() {
        return Err(RuntimeError::TypeError {
            expected: "block code",
            got: map.code,
        });
    }
    Ok(map.code)
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

fn find_enclosing_method_idx(frames: &[Frame]) -> Option<usize> {
    frames.iter().rposition(|f| !f.is_block)
}

fn find_enclosing_temp_array(vm: &VM, frames: &[Frame]) -> Option<Value> {
    let nil = vm.special.nil.raw();
    frames.iter().rev().find_map(|frame| {
        if frame.temp_array.raw() != nil {
            Some(frame.temp_array)
        } else {
            None
        }
    })
}

fn find_enclosing_holder(vm: &VM, frames: &[Frame]) -> (Value, u32) {
    let nil = vm.special.nil;
    for frame in frames.iter().rev() {
        if frame.holder.raw() != nil.raw() {
            return (frame.holder, frame.holder_slot_index);
        }
    }
    (nil, 0)
}

fn current_frame_index(state: &InterpreterState) -> Option<usize> {
    if state.frames.is_empty() {
        None
    } else {
        Some(state.frames.len() - 1)
    }
}

fn is_truthy(vm: &VM, value: Value) -> bool {
    let nil = vm.special.nil.raw();
    let false_obj = vm.special.false_obj.raw();
    let raw = value.raw();
    raw != nil && raw != false_obj
}

fn get_register(frame: &Frame, reg: u16) -> Result<Value, RuntimeError> {
    frame
        .registers
        .get(reg as usize)
        .copied()
        .ok_or(RuntimeError::TypeError {
            expected: "register",
            got: Value::from_i64(reg as i64),
        })
}

fn set_register(
    frame: &mut Frame,
    reg: u16,
    value: Value,
) -> Result<(), RuntimeError> {
    if let Some(slot) = frame.registers.get_mut(reg as usize) {
        *slot = value;
        Ok(())
    } else {
        Err(RuntimeError::TypeError {
            expected: "register",
            got: Value::from_i64(reg as i64),
        })
    }
}

fn load_stack_slot(frame: &mut Frame, offset: u32, nil: Value) -> Value {
    let idx = offset as usize;
    if idx >= frame.registers.len() {
        frame.registers.resize(idx + 1, nil);
    }
    frame.registers[idx]
}

fn store_stack_slot(frame: &mut Frame, offset: u32, value: Value, nil: Value) {
    let idx = offset as usize;
    if idx >= frame.registers.len() {
        frame.registers.resize(idx + 1, nil);
    }
    frame.registers[idx] = value;
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
    let (proxy, special, intern_table, assoc_map, dictionary) = (
        &mut vm.heap_proxy,
        &mut vm.special,
        &mut vm.intern_table,
        &mut vm.assoc_map,
        &mut vm.dictionary,
    );
    let mut roots = InterpreterRoots {
        acc: &mut state.acc,
        frames: &mut state.frames,
        special,
        intern_table,
        assoc_map,
        dictionary,
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
    if source_map.value_count() != 0 {
        return Err(RuntimeError::Unimplemented {
            message: "extend: assignable slot",
        });
    }

    let mut new_slots: Vec<Slot> = Vec::new();
    for slot in unsafe { source_map.slots() } {
        if !slot.is_constant() {
            return Err(RuntimeError::Unimplemented {
                message: "extend: assignable slot",
            });
        }
        new_slots.push(*slot);
    }

    let mut scratch = vec![target, source, source_map_val];
    let new_map = with_roots(vm, state, &mut scratch, |proxy, roots| unsafe {
        let map_map = roots.special.map_map;
        crate::alloc::append_constant_slots(
            proxy,
            roots,
            (*target_ptr).map,
            map_map,
            &new_slots,
        )
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
    use heap::HeapSettings;
    use object::{Map, ObjectType, SlotFlags, VMString};
    use parser::{Lexer, Parser};

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

    fn parse_source(src: &str) -> Vec<parser::ast::Expr> {
        let lexer = Lexer::from_str(src);
        Parser::new(lexer)
            .map(|r| r.expect("parse error"))
            .collect()
    }

    fn run_source(src: &str) -> Result<Value, RuntimeError> {
        let exprs = parse_source(src);
        let code_desc = Compiler::compile(&exprs).expect("compile error");
        let mut vm = bootstrap(test_settings());
        let code_val = materialize(&mut vm, &code_desc);
        interpret(&mut vm, code_val)
    }

    fn run_source_with_vm(src: &str) -> Result<(VM, Value), RuntimeError> {
        let exprs = parse_source(src);
        let code_desc = Compiler::compile(&exprs).expect("compile error");
        let mut vm = bootstrap(test_settings());
        let code_val = materialize(&mut vm, &code_desc);
        let value = interpret(&mut vm, code_val)?;
        Ok((vm, value))
    }

    fn run_source_with_receiver(
        src: &str,
        receiver: Value,
    ) -> Result<Value, RuntimeError> {
        let exprs = parse_source(src);
        let code_desc = Compiler::compile(&exprs).expect("compile error");
        let mut vm = bootstrap(test_settings());
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
        let value = run_source("\"hello\"").expect("interpret error");
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
    fn interpret_local_assignment() {
        let value = run_source("x = 5. x").expect("interpret error");
        assert!(value.is_fixnum());
        assert_eq!(unsafe { value.to_i64() }, 5);
    }

    #[test]
    fn interpret_global_store_load() {
        let value =
            run_source("{ x := (Y := 5) }. Y").expect("interpret error");
        assert!(value.is_fixnum());
        assert_eq!(unsafe { value.to_i64() }, 5);
    }

    #[test]
    fn interpret_data_object_creation() {
        let value = run_source("{ x = 5 }").expect("interpret error");
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
        let value = run_source("[1]").expect("interpret error");
        assert!(value.is_ref());
        let header: &Header = unsafe { value.as_ref() };
        assert_eq!(header.object_type(), ObjectType::Block);
    }

    #[test]
    fn interpret_message_not_understood() {
        let err = run_source("5 foo").expect_err("expected error");
        assert!(matches!(err, RuntimeError::MessageNotUnderstood { .. }));
    }

    #[test]
    fn interpret_temp_store_load() {
        let value = run_source("x = 5. [ x ]. x").expect("interpret error");
        assert!(value.is_fixnum());
        assert_eq!(unsafe { value.to_i64() }, 5);
    }

    #[test]
    fn interpret_block_updates_captured_mutable() {
        let value = run_source("i := 0. [ i := i _FixnumAdd: 1 ] call. i")
            .expect("interpret error");
        assert!(value.is_fixnum());
        assert_eq!(unsafe { value.to_i64() }, 1);
    }

    #[test]
    fn interpret_nested_block_reads_capture() {
        let value =
            run_source("i := 0. [ [ i ] call ] call").expect("interpret error");
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
            i := 0. [ i <= 1 ] call",
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

    fn lookup_dictionary_value(vm: &VM, name: &str) -> Option<Value> {
        let sym = vm.intern_table.get(name)?;
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
    fn dictionary_fixnum_matches_traits() {
        let vm = bootstrap(test_settings());
        let fixnum_value =
            lookup_dictionary_value(&vm, "Fixnum").expect("Fixnum missing");
        assert_eq!(fixnum_value.raw(), vm.special.fixnum_traits.raw());
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
        match err {
            RuntimeError::Unimplemented { .. } => {}
            other => panic!("expected Unimplemented, got {other:?}"),
        }
    }

    #[test]
    fn extend_with_rejects_code() {
        let err = run_source("o = { }. Object _Extend: o With: { x = 1. 2 }")
            .expect_err("expected error");
        assert!(matches!(err, RuntimeError::Unimplemented { .. }));
    }
}
