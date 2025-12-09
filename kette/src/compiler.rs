use crate::{
    Array, Block, Handle, Instruction, Message, ObjectType, Quotation, VMShared,
};

pub struct BytecodeCompiler {}

impl BytecodeCompiler {
    pub fn compile(vm: &VMShared, body: Handle<Array>) -> Block {
        let mut instructions = Vec::new();
        for word in body.fields() {
            println!("obj1");

            if let Some(value) = word.as_tagged_fixnum::<i64>() {
                instructions.push(Instruction::PushFixnum {
                    value: value.as_i64(),
                });
                continue;
            }

            println!("obj2");

            // SAFETY: no gc here
            let obj = unsafe { word.as_heap_handle_unchecked() };

            let message =
                match obj.header.object_type().expect("must be object") {
                    ObjectType::Slot
                    | ObjectType::Array
                    | ObjectType::ByteArray
                    | ObjectType::Method => {
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
                        unreachable!("obj {:?} invalid", word)
                    }
                };

            println!("test");
            // TODO: implement the resend and delegate
            let ba = message.bytearray_handle();
            if ba == vm.specials.message_self {
                instructions.push(Instruction::PushSelf);
                continue;
            }

            instructions.push(Instruction::Send { message })
        }

        Block { instructions }
    }
}
