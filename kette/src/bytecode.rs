use std::ptr::NonNull;

use crate::Value;

#[allow(unused)]
#[derive(Debug, Clone, Copy)]
pub struct Message(usize);

#[derive(Debug, Clone, Copy)]
pub enum Instruction {
    Send {
        message: Message,
    },
    SelfSend {
        message: Message,
    },
    SuperSend {
        message: Message,
    },
    DelegateSend {
        message: Message,
    },
    CreateFixnum {
        value: i64,
    },
    CreateFloat {
        value: f64,
    },
    CreateArray {
        size: usize,
        fill: Value,
    },
    CreateByteArray {
        size: usize,
        data: Option<NonNull<u8>>,
    },
    CreateObject {
        // map: View<SlotMap>,
    },
    Return,
}

// TODO: replace instructions to actual byte instructions
// use a design similar to arm, 8 byte opcode + 24 byte data?
// we can also do it like riscV and add additional compressed instructions
// but at least for high level "parsing", we should keep something like the current instructions
// we can also optimize this further and inline the instructions into the Block itself
#[allow(unused)]
pub struct Block {
    instructions: Vec<Instruction>,
}
