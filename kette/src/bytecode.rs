use parking_lot::RwLock;

use crate::{
    Handle, Message, PrimitiveMessageIndex, Quotation, SlotMap, Tagged, Value,
};

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

    // Optimization / Testing / Friendly User interface
    SendPrimitive { id: PrimitiveMessageIndex },

    // Debug / friendly user interface
    SendNamed { message: &'static str },
    SuperSendNamed { message: &'static str },
    DelegatSendeNamed { message: &'static str },

    AllocateSlotObject { map: Tagged<SlotMap> },
}

// TODO: replace instructions to actual byte instructions
// use a design similar to arm, 8 byte opcode + 24 byte data?
// we can also do it like riscV and add additional compressed instructions
// but at least for high level "parsing", we should keep something like the current instructions
// we can also optimize this further and inline the instructions into the Block itself
#[derive(Debug)]
pub struct Block {
    pub instructions: Vec<Instruction>,
}

// TODO: make this faster and more cache friendly
// the Block -> Vec is also bad, it should be inlined
// TODO: current thing will break on resize
#[derive(Debug, Default)]
pub struct CodeHeap {
    blocks: RwLock<Vec<Block>>,
}

impl CodeHeap {
    pub fn new() -> Self {
        Self {
            blocks: RwLock::new(Vec::with_capacity(1024)),
        }
    }

    pub fn push(&self, block: Block) -> &Block {
        let mut blocks = self.blocks.write();
        blocks.push(block);
        // SAFETY: this is mostly safe, about the unwrap_unchecked, it must exist we just pushed it
        unsafe {
            (blocks.last().unwrap_unchecked() as *const Block)
                .as_ref()
                .unwrap_unchecked()
        }
    }
}
