use std::{alloc::Layout, mem, ptr};

use crate::{
    Handle, Header, HeapObject, Message, Object, ObjectKind, ObjectType,
    PrimitiveMessageIndex, Quotation, SlotMap, Tagged, Value, Visitable,
    Visitor,
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
    StackToReturn,
    ReturnToStack,
    // TODO implement this
    // PushFloat {
    //     value: f64,
    // },
    Return,
    // TODO: implement non-local returns (ways to exit quotations)
    // NonLocalReturn

    // Optimization / Testing / Friendly User interface
    SendPrimitive { id: PrimitiveMessageIndex },

    // Debug / friendly user interface
    SendNamed { message: &'static str },
    SuperSendNamed { message: &'static str },
    DelegatSendeNamed { message: &'static str },

    CreateSlotObject { map: Handle<SlotMap> },
}

// TODO: replace instructions to actual byte instructions
#[repr(C)]
#[derive(Debug)]
pub struct Code {
    pub header: Header,
    pub size: Tagged<usize>,
    pub instructions: [Instruction; 0],
}

impl Code {
    /// Initialize with instructions
    pub fn init_with_data(&mut self, instructions: &[Instruction]) {
        self.header = Header::new_object(ObjectType::Code);
        self.size = instructions.len().into();

        // SAFETY: safe if allocation is correct size (guaranteed by Allocator)
        unsafe {
            ptr::copy_nonoverlapping(
                instructions.as_ptr(),
                self.instructions.as_mut_ptr(),
                instructions.len(),
            )
        };
    }

    #[inline]
    #[allow(clippy::len_without_is_empty)]
    pub fn len(&self) -> usize {
        self.size.into()
    }

    #[inline]
    pub fn instructions(&self) -> &[Instruction] {
        let len = self.len();
        // SAFETY: header guarantees length
        unsafe { std::slice::from_raw_parts(self.instructions.as_ptr(), len) }
    }

    #[inline]
    pub fn instructions_mut(&mut self) -> &mut [Instruction] {
        let len = self.len();
        // SAFETY: header guarantees length
        unsafe {
            std::slice::from_raw_parts_mut(self.instructions.as_mut_ptr(), len)
        }
    }

    pub fn required_layout(count: usize) -> Layout {
        let head = Layout::new::<Code>();
        let instructions_layout =
            Layout::array::<Instruction>(count).expect("create valid layout");
        let (layout, _) = head
            .extend(instructions_layout)
            .expect("create valid layout");
        layout
    }
}

impl HeapObject for Code {
    const KIND: ObjectKind = ObjectKind::Object;
    const TYPE_BITS: u8 = ObjectType::Code as u8;

    fn heap_size(&self) -> usize {
        mem::size_of::<Self>() + self.len() * mem::size_of::<Instruction>()
    }
}

impl Object for Code {}

impl Visitable for Code {
    fn visit_edges_mut(&mut self, visitor: &mut impl Visitor) {
        // We must visit instructions because they contain Handles and Values!
        for instr in self.instructions_mut() {
            match instr {
                Instruction::Send { message }
                | Instruction::SuperSend { message }
                | Instruction::DelegateSend { message } => {
                    visitor.visit_mut(message.as_value())
                }
                Instruction::PushValue { value } => visitor.visit_mut(*value),
                Instruction::PushQuotaton { value } => {
                    visitor.visit_mut(value.as_value())
                }
                Instruction::CreateSlotObject { map } => {
                    visitor.visit_mut(map.as_value())
                }
                // Primitives/Fixnums/ControlFlow do not hold heap references
                _ => {}
            }
        }
    }

    fn visit_edges(&self, visitor: &impl Visitor) {
        for instr in self.instructions() {
            match instr {
                Instruction::Send { message }
                | Instruction::SuperSend { message }
                | Instruction::DelegateSend { message } => {
                    visitor.visit(message.as_value())
                }

                Instruction::PushValue { value } => visitor.visit(*value),
                Instruction::PushQuotaton { value } => {
                    visitor.visit(value.as_value())
                }
                Instruction::CreateSlotObject { map } => {
                    visitor.visit(map.as_value())
                }
                // Primitives/Fixnums/ControlFlow do not hold heap references
                _ => {}
            }
        }
    }
}
