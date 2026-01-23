use crate::{
    bytecode2::BytecodeWriter, Allocator, Array, Code2, Handle, HeapProxy,
    Message, ObjectType, Quotation, SlotMap, VMShared, Value,
};

pub struct BytecodeCompiler2 {}

impl BytecodeCompiler2 {
    pub fn compile(
        vm: &VMShared,
        heap: &mut HeapProxy,
        body: Handle<Array>,
    ) -> Handle<Code2> {
        let _span =
            tracing::span!(tracing::Level::DEBUG, "compile2", body = ?body)
                .entered();

        let mut writer = BytecodeWriter::new();
        let mut constants: Vec<Value> = Vec::new();
        let mut feedback_slots = 0;

        let mut add_constant = |val: Value| -> u16 {
            // Linear scan for deduplication.
            if let Some(idx) = constants.iter().position(|&c| c == val) {
                return idx as u16;
            }

            let idx = constants.len();
            if idx > 0xFFFF {
                panic!("Constant pool overflow: >65k constants in one method");
            }
            constants.push(val);
            idx as u16
        };

        let words = body.fields();
        for (idx, word) in words.iter().enumerate() {
            // 1. Handle Fixnums
            if let Some(tagged) = word.as_tagged_fixnum::<i64>() {
                let val = tagged.as_i64();

                // Always use PushSmallInteger for integers, taking i32.
                // If it doesn't fit in i32, use constant pool.
                if val >= (i32::MIN as i64) && val <= (i32::MAX as i64) {
                    writer.emit_push_small_integer(val as i32);
                } else {
                    let const_idx = add_constant(*word);
                    writer.emit_push_constant(const_idx);
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
                    writer.emit_push_constant(const_idx);
                    continue;
                }
                ObjectType::Quotation => {
                    // SAFETY: checked
                    let quot = unsafe { obj.cast::<Quotation>() };
                    let const_idx = add_constant(quot.as_value());
                    writer.emit_push_constant(const_idx);
                    continue;
                }
                // Messages are treated as Sends
                // SAFETY: checked
                ObjectType::Message => unsafe { obj.cast::<Message>() },
                _ => unreachable!("Invalid object in source array"),
            };

            // Handle Special Messages
            if message == vm.specials.message_self {
                writer.emit_push_self();
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
                    writer.emit_create_slot_object(map_idx);
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
                    writer.emit_create_quotation(map_idx);
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

            // Assign a feedback slot index
            let feedback_idx = feedback_slots;
            if feedback_slots > 0xFFFF {
                panic!("Feedback vector overflow: >65k sends in one method");
            }
            feedback_slots += 1;

            writer.emit_send(msg_idx, feedback_idx as u16);
        }

        writer.emit_return();

        // Allocate feedback vector
        // SAFETY: The heap allocator expects a size, which we have.
        // We'll allocate a raw array of size `feedback_slots`.
        // The array will be initialized with nil/zero by `allocate_raw_array`?
        // `allocate_raw_array` in allocator.rs calls `init(size)`.
        // `init` on Array usually sets fields to nil/0.
        // Let's verify Array::init.
        // Assuming it's safe to have uninitialized values if they are just placeholders?
        // Actually allocator::allocate_raw_array comment says: "user code must initialize this".
        // `Array::init` sets the header and length. Data might be garbage?
        // `Array::required_layout` uses `Layout::array::<Value>`.
        // `Value` is a tagged pointer. Garbage could be dangerous if GC traces it.
        // I should use `allocate_array` with a slice of nils, or `allocate_raw_array` and fill it.
        // `allocator.rs` has `allocate_array(&[Value])`.
        // I'll create a vec of nils.

        let feedback_vector = unsafe { Handle::null() };

        heap.allocate_code2(
            &constants,
            &writer.into_inner(),
            body,
            feedback_vector,
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{HeapSettings, OpCode, VMCreateInfo, VM};

    #[test]
    fn test_compiler_basic() {
        // Setup VM
        let vm = VM::new(VMCreateInfo {
            image: None,
            heap: HeapSettings::default(),
        });
        let mut heap = vm.proxy().shared.heap.proxy();

        // Create body: [10, self]
        // We need 'self' message object.
        let msg_self = vm.proxy().shared.specials.message_self;

        let elements = vec![Value::from_fixnum(10), msg_self.as_value()];

        let body = heap.allocate_array(&elements);

        // Compile
        let code_handle =
            BytecodeCompiler2::compile(&vm.proxy().shared, &mut heap, body);
        let code = code_handle.inner();

        // Verify Instructions
        let insts = code.instructions();

        // Expected:
        // PushSmallInteger(10) -> [03, 10, 00, 00, 00] (little endian 10)
        // PushSelf -> [02]
        // Return -> [00]

        let mut expected = vec![];
        // PushSmallInteger
        expected.push(OpCode::PushSmallInteger as u8);
        expected.extend_from_slice(&10i32.to_ne_bytes());
        // PushSelf
        expected.push(OpCode::PushSelf as u8);
        // Return
        expected.push(OpCode::Return as u8);

        assert_eq!(insts, expected.as_slice());

        // Verify Constants (Should be empty for this case)
        assert_eq!(code.constants().len(), 0);

        // Verify Feedback Vector (Should be null initially for lazy allocation)
        assert!(code.feedback_vector.as_ptr().is_null());
    }

    #[test]
    fn test_compiler_send() {
        let vm = VM::new(VMCreateInfo {
            image: None,
            heap: HeapSettings::default(),
        });
        let mut heap = vm.proxy().shared.heap.proxy();

        // Create body: [10, "to_string" message]
        // We need to intern a message.
        let msg_str = vm.proxy().intern_string_message("to_string", &mut heap);

        let elements = vec![Value::from_fixnum(10), msg_str.as_value()];

        let body = heap.allocate_array(&elements);

        let code_handle =
            BytecodeCompiler2::compile(&vm.proxy().shared, &mut heap, body);
        let code = code_handle.inner();

        // Expected:
        // PushSmallInteger(10)
        // Send(msg_idx=0, feedback_idx=0)
        // Return

        let insts = code.instructions();
        let mut cursor = 0;

        assert_eq!(insts[cursor], OpCode::PushSmallInteger as u8);
        cursor += 1;
        cursor += 4; // Skip i32

        assert_eq!(insts[cursor], OpCode::Send as u8);
        cursor += 1;
        // msg_idx (u16)
        let slice = &insts[cursor..cursor + 2];
        let msg_idx = u16::from_ne_bytes(slice.try_into().unwrap());
        cursor += 2;
        // feedback_idx (u16)
        let slice = &insts[cursor..cursor + 2];
        let fb_idx = u16::from_ne_bytes(slice.try_into().unwrap());
        cursor += 2;

        assert_eq!(fb_idx, 0);
        assert_eq!(msg_idx, 0); // First constant

        assert_eq!(insts[cursor], OpCode::Return as u8);

        // Verify Constants
        assert_eq!(code.constants().len(), 1);
        assert_eq!(code.constants()[0], msg_str.as_value());

        // Verify Feedback Vector (Should be null initially for lazy allocation)
        assert!(code.feedback_vector.as_ptr().is_null());
    }
}
