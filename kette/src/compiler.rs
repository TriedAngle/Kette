use crate::{
    Allocator, Array, Code, Handle, HeapProxy, Instruction, Message,
    ObjectType, OpCode, Quotation, SlotMap, VMShared, Value,
};

pub struct BytecodeCompiler {}

impl BytecodeCompiler {
    pub fn compile(
        vm: &VMShared,
        heap: &mut HeapProxy,
        body: Handle<Array>,
    ) -> Handle<Code> {
        let _span =
            tracing::span!(tracing::Level::DEBUG, "compile", body = ?body)
                .entered();

        // i24 constants
        const MAX_I24: i64 = 8_388_607; // 2^23 - 1
        const MIN_I24: i64 = -8_388_608; // -2^23

        let mut instructions: Vec<Instruction> = Vec::new();
        let mut constants: Vec<Value> = Vec::new();

        let mut add_constant = |val: Value| -> u32 {
            // Linear scan for deduplication.
            if let Some(idx) = constants.iter().position(|&c| c == val) {
                return idx as u32;
            }

            let idx = constants.len();
            // Panic if we exceed 24-bit address space (very unlikely)
            // if this ever happens, consider adding extended instructions
            if idx > 0xFFFFFF {
                panic!("Constant pool overflow: >16M constants in one method");
            }
            constants.push(val);
            idx as u32
        };

        let words = body.fields();
        for (idx, word) in words.iter().enumerate() {
            // 1. Handle Fixnums
            if let Some(tagged) = word.as_tagged_fixnum::<i64>() {
                let val = tagged.as_i64();

                if (MIN_I24..=MAX_I24).contains(&val) {
                    // Fits in 24 bits!
                    instructions.push(Instruction::new_data(
                        OpCode::PushSmallInteger,
                        val as u32,
                    ));
                } else {
                    // Too big, use constant pool
                    let const_idx = add_constant(*word);
                    instructions.push(Instruction::new_data(
                        OpCode::PushConstant,
                        const_idx,
                    ));
                }
                continue;
            }

            // SAFETY: We checked it's not a fixnum, so it must be a heap object
            let obj = unsafe { word.as_heap_handle_unchecked() };

            // Skip Map Definitions (handled by lookback later)
            if let Some(_map) = obj.downcast_ref::<SlotMap>() {
                continue;
            }

            // Dispatch based on Object Type
            let message = match obj.header.object_type().expect("valid object")
            {
                // Literals: Push as constants
                ObjectType::Slot
                | ObjectType::Array
                | ObjectType::ByteArray
                | ObjectType::Float
                | ObjectType::Thread
                | ObjectType::BigNum => {
                    let const_idx = add_constant(obj.as_value());
                    instructions.push(Instruction::new_data(
                        OpCode::PushConstant,
                        const_idx,
                    ));
                    continue;
                }
                ObjectType::Quotation => {
                    // SAFETY: checked
                    let quot = unsafe { obj.cast::<Quotation>() };
                    let const_idx = add_constant(quot.as_value());
                    instructions.push(Instruction::new_data(
                        OpCode::PushConstant,
                        const_idx,
                    ));
                    continue;
                }
                // Messages are treated as Sends
                // SAFETY: checked
                ObjectType::Message => unsafe { obj.cast::<Message>() },
                _ => unreachable!("Invalid object in source array"),
            };

            // Handle Special Messages
            if message == vm.specials.message_self {
                instructions.push(Instruction::new(OpCode::PushSelf));
                continue;
            }

            if message == vm.specials.message_create_object {
                // Lookback for the Map
                if idx == 0 {
                    panic!("CreateSlotObject cannot be the first instruction");
                }
                let prior = words[idx - 1];
                // SAFETY: this is safe
                let obj_handle = unsafe { prior.as_heap_handle_unchecked() };

                if let Some(_map) = obj_handle.downcast_ref::<SlotMap>() {
                    let map_idx = add_constant(prior);
                    instructions.push(Instruction::new_data(
                        OpCode::CreateSlotObject,
                        map_idx,
                    ));
                } else {
                    panic!(
                        "CreateSlotObject requires a Map immediately before it"
                    );
                }
                continue;
            }

            if message == vm.specials.message_create_quotation {
                // Lookback for the Map
                if idx == 0 {
                    panic!("CreateQuotation cannot be the first instruction");
                }
                let prior = words[idx - 1];
                // SAFETY: this is safe
                let obj_handle = unsafe { prior.as_heap_handle_unchecked() };

                if let Some(_map) = obj_handle.downcast_ref::<SlotMap>() {
                    let map_idx = add_constant(prior);
                    instructions.push(Instruction::new_data(
                        OpCode::CreateQuotation,
                        map_idx,
                    ));
                } else {
                    panic!(
                        "CreateQuotation requires a Map immediately before it"
                    );
                }
                continue;
            }

            // 5. Default Send
            // This also reuses the constant index if we send the same message multiple times!
            let msg_idx = add_constant(message.as_value());
            instructions.push(Instruction::new_data(OpCode::Send, msg_idx));
        }

        instructions.push(Instruction::new(OpCode::Return));

        heap.allocate_code(&constants, &instructions, body)
    }
}
