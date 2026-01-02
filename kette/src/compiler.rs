use crate::{
    Array, Block, Handle, Instruction, Message, ObjectType, Quotation, SlotMap,
    VMShared,
};

pub struct BytecodeCompiler {}

impl BytecodeCompiler {
    pub fn compile(vm: &VMShared, body: Handle<Array>) -> Block {
        let _span =
            tracing::span!(tracing::Level::DEBUG, "compile", body = ?body )
                .entered();
        let mut instructions = Vec::new();
        let words = body.fields();
        for (idx, word) in words.iter().enumerate() {
            if let Some(value) = word.as_tagged_fixnum::<i64>() {
                instructions.push(Instruction::PushFixnum {
                    value: value.as_i64(),
                });
                continue;
            }

            // SAFETY: no gc here
            let obj = unsafe { word.as_heap_handle_unchecked() };

            if let Some(_map) = obj.downcast_ref::<SlotMap>() {
                continue;
            }

            let message =
                match obj.header.object_type().expect("must be object") {
                    ObjectType::Slot
                    | ObjectType::Array
                    | ObjectType::ByteArray
                    | ObjectType::Float
                    | ObjectType::Thread
                    | ObjectType::BigNum => {
                        instructions.push(Instruction::PushValue {
                            value: obj.as_value(),
                        });
                        continue;
                    }
                    ObjectType::Quotation => {
                        // TODO: potentially inline
                        // SAFETY: safe
                        let quot = unsafe {
                            word.as_heap_handle_unchecked().cast::<Quotation>()
                        };
                        instructions
                            .push(Instruction::PushQuotaton { value: quot });
                        continue;
                    }
                    // SAFETY: checked
                    ObjectType::Message => unsafe { obj.cast::<Message>() },
                    ObjectType::Max | ObjectType::Activation => {
                        unreachable!("object {:?} is invalid here", word)
                    }
                };

            // TODO: implement the resend and delegate
            if message == vm.specials.message_self {
                instructions.push(Instruction::PushSelf);
                continue;
            }

            if message == vm.specials.message_create_object {
                let prior = words[idx - 1];

                // SAFETY: must be by definition
                let mut obj = unsafe { prior.as_heap_handle_unchecked() };
                if let Some(_map) = obj.downcast_mut::<SlotMap>() {
                    let map =
                        // SAFETY: checked 
                        unsafe { prior.as_heap_handle_unchecked().cast() };
                    instructions.push(Instruction::CreateSlotObject { map });
                } else {
                    panic!(
                        "invalid state, CreateSlotObject requires map in parsing"
                    )
                }
                continue;
            }

            instructions.push(Instruction::Send { message })
        }

        instructions.push(Instruction::Return);

        Block { instructions }
    }
}
