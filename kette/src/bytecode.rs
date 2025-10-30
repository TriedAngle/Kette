use std::ptr::NonNull;

use crate::{ActorId, SlotMap, TaggedValue, View, interning::InternedId};

#[derive(Debug, Clone, Copy)]
pub struct Message(InternedId);

#[derive(Debug, Clone, Copy)]
pub enum Instruction {
    FiberYield,
    ActorYield {
        id: ActorId,
    },
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
        fill: TaggedValue,
    },
    CreateByteArray {
        size: usize,
        data: Option<NonNull<u8>>,
    },
    CreateObject {
        map: View<SlotMap>,
    },
    Return,
}

pub struct Block {
    instructions: Vec<Instruction>,
}
