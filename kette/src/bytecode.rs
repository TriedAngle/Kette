use std::{alloc::Layout, mem, ptr};

use crate::{
    Header, HeapObject, Object, ObjectKind, ObjectType, Value, Visitable,
    Visitor,
};

#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OpCode {
    /// Returns from the current activation.
    Return = 0x00,

    /// Pushes a value from the constant pool.
    /// Payload: Index in constant pool.
    PushConstant = 0x01,

    /// Pushes the receiver (self) onto the stack.
    PushSelf = 0x02,

    /// Push Small Integer
    PushSmallInteger = 0x03,

    /// Sends a message.
    /// Payload: Index of the Selector (Message) in the constant pool.
    Send = 0x04,

    /// Send a primitive message
    SendPrimitive = 0x05,

    /// Creates a slot object from a map.
    /// Payload: Index of the SlotMap in the constant pool.
    CreateSlotObject = 0x06,

    /// Move top of stack to return stack
    PushReturn = 0x07,
    /// Move top of return stack to stack
    PopReturn = 0x08,
}

impl OpCode {
    #[inline(always)]
    pub fn from_u8(v: u8) -> Self {
        // SAFETY: This is unsafe in production without checks,
        // but for this VM stage we assume the compiler is correct.
        unsafe { std::mem::transmute(v) }
    }
}

/// A 32-bit fixed-width instruction.
/// Layout: [8-bit OpCode] [24-bit Operand]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(transparent)]
pub struct Instruction(u32);

impl Instruction {
    /// Create a new instruction from an OpCode and a 24-bit operand.
    #[inline(always)]
    pub fn new(op: OpCode) -> Self {
        let raw = (op as u32) << 24;
        Self(raw)
    }
    /// Create a new instruction from an OpCode and a 24-bit operand.
    #[inline(always)]
    pub fn new_data(op: OpCode, operand: u32) -> Self {
        debug_assert!(operand <= 0xFFFFFF, "Operand overflow");
        let raw = ((op as u32) << 24) | (operand & 0xFFFFFF);
        Self(raw)
    }

    /// Extract the OpCode.
    #[inline(always)]
    pub fn opcode(self) -> OpCode {
        OpCode::from_u8((self.0 >> 24) as u8)
    }

    /// Extract the 24-bit operand.
    #[inline(always)]
    pub fn operand(self) -> u32 {
        self.0 & 0xFFFFFF
    }

    /// Get raw u32 representation (useful for debugging/serialization).
    #[inline(always)]
    pub fn raw(self) -> u32 {
        self.0
    }

    #[inline(always)]
    pub fn signed_operand(self) -> i32 {
        // 1. Mask to get the 24 bits (0x00FFFFFF)
        // 2. Shift left by 8 to move the sign bit (bit 23) to the MSB (bit 31)
        // 3. Arithmetic shift right by 8 to sign-extend back down
        let raw = self.0 & 0xFFFFFF;
        (raw << 8) as i32 >> 8
    }
}

#[repr(C)]
#[derive(Debug)]
pub struct Code {
    pub header: Header,
    pub const_count: u32,
    pub inst_count: u32,
    // Memory Layout:
    // 1. [Value; const_count]
    // 2. [Instruction; inst_count]
    data: [u8; 0],
}

impl Code {
    pub fn required_layout(consts: usize, insts: usize) -> Layout {
        let base = Layout::new::<Code>();
        let (with_consts, _) = base
            .extend(Layout::array::<Value>(consts).unwrap())
            .unwrap();
        // Uses Instruction type for layout calculation
        let (final_layout, _) = with_consts
            .extend(Layout::array::<Instruction>(insts).unwrap())
            .unwrap();
        final_layout
    }

    /// Initialize the raw memory with data.
    pub fn init_with_data(
        &mut self,
        constants: &[Value],
        instructions: &[Instruction],
    ) {
        self.header = Header::new_object(ObjectType::Code);
        self.const_count = constants.len() as u32;
        self.inst_count = instructions.len() as u32;

        unsafe {
            let ptr_base = self.data.as_mut_ptr();

            // 1. Copy Constants
            let ptr_consts = ptr_base as *mut Value;
            ptr::copy_nonoverlapping(
                constants.as_ptr(),
                ptr_consts,
                constants.len(),
            );

            // 2. Copy Instructions
            // Offset by size of constant pool
            let offset_bytes = constants.len() * mem::size_of::<Value>();
            // Cast to *mut Instruction
            let ptr_insts = ptr_base.add(offset_bytes) as *mut Instruction;

            ptr::copy_nonoverlapping(
                instructions.as_ptr(),
                ptr_insts,
                instructions.len(),
            );
        }
    }

    pub fn constants(&self) -> &[Value] {
        unsafe {
            let ptr = self.data.as_ptr() as *const Value;
            std::slice::from_raw_parts(ptr, self.const_count as usize)
        }
    }

    pub fn instructions(&self) -> &[Instruction] {
        unsafe {
            let offset_bytes =
                self.const_count as usize * mem::size_of::<Value>();
            let ptr =
                self.data.as_ptr().add(offset_bytes) as *const Instruction;
            std::slice::from_raw_parts(ptr, self.inst_count as usize)
        }
    }
}

impl Object for Code {}

impl HeapObject for Code {
    const KIND: ObjectKind = ObjectKind::Object;
    const TYPE_BITS: u8 = ObjectType::Code as u8;
    fn heap_size(&self) -> usize {
        Code::required_layout(
            self.const_count as usize,
            self.inst_count as usize,
        )
        .size()
    }
}

impl Visitable for Code {
    fn visit_edges_mut(&mut self, visitor: &mut impl Visitor) {
        let count = self.const_count as usize;
        let ptr = self.data.as_mut_ptr() as *mut Value;
        // Only visit constants
        let constants = unsafe { std::slice::from_raw_parts(ptr, count) };
        for &val in constants {
            visitor.visit_mut(val);
        }
    }

    fn visit_edges(&self, visitor: &impl Visitor) {
        for &val in self.constants() {
            visitor.visit(val);
        }
    }
}
