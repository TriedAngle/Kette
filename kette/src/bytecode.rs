use crate::{Handle, Message, Quotation, Tagged, Value};

#[derive(Debug, Clone, Copy)]
pub enum Instruction {
    Send { message: Handle<Message> },
    SuperSend { message: Handle<Message> },
    DelegateSend { message: Handle<Message> },
    PushSelf,
    PushValue { value: Value },
    PushFixnum { value: i64 },
    PushQuotaton { value: Handle<Quotation> },
    // TODO implement this
    // PushFloat {
    //     value: f64,
    // },
    Return,

    // Debug implementations
    SendNamed { message: &'static str },
    SuperSendNamed { message: &'static str },
    DelegatSendeNamed { message: &'static str },
}

// TODO: replace instructions to actual byte instructions
// use a design similar to arm, 8 byte opcode + 24 byte data?
// we can also do it like riscV and add additional compressed instructions
// but at least for high level "parsing", we should keep something like the current instructions
// we can also optimize this further and inline the instructions into the Block itself
#[allow(unused)]
pub struct Block {
    pub instructions: Vec<Instruction>,
}
