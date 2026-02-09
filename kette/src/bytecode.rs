use std::{alloc::Layout, mem, ptr};

use crate::{
    Array, Handle, Header, HeapObject, Object, ObjectKind, ObjectType, Value,
    Visitable, Visitor,
};

#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OpCode {
    /// Returns from the current activation.
    Return = 0x00,

    /// Pushes a value from the constant pool.
    /// Payload: Index in constant pool (u16).
    PushConstant = 0x01,

    /// Pushes the receiver (self) onto the stack.
    PushSelf = 0x02,

    /// Push Small Integer
    /// Payload: i32 value.
    PushSmallInteger = 0x03,

    /// Sends a message.
    /// Payload: Index of the Selector (Message) in the constant pool (u16).
    /// Payload: Index of the Feedback Vector slot (u16).
    Send = 0x04,

    /// Send a primitive message
    /// Payload: Primitive Index (u16).
    SendPrimitive = 0x05,

    /// Send to any super
    /// Payload: Index of Selector (u16).
    /// Payload: Feedback Index (u16).
    SendSuper = 0x06,

    /// send to a specific parent
    /// Payload: Index of the Name of the parent in the constant pool (u16).
    /// Payload: Index of Selector (u16).
    /// Payload: Feedback Index (u16).
    SendParent = 0x07,

    /// Creates a slot object from a map.
    /// Payload: Index of the Map in the constant pool (u16).
    CreateSlotObject = 0x08,

    /// Creates a quotation object from a map
    /// Payload: Index of the Map in the constant pool (u16).
    CreateQuotation = 0x09,

    /// Move top of stack to return stack
    PushReturn = 0x0A,
    /// Move top of return stack to stack
    PopReturn = 0x0B,
}

impl OpCode {
    #[inline(always)]
    #[must_use]
    pub fn from_u8(v: u8) -> Self {
        // SAFETY: OpCode is repr(u8) and all valid opcodes are defined
        unsafe { std::mem::transmute(v) }
    }
}

#[repr(C)]
#[derive(Debug)]
pub struct Code {
    pub header: Header,
    pub const_count: u32,
    /// Size of instructions in bytes
    pub inst_size: u32,
    /// Number of Send sites
    pub feedback_slot_count: u32,
    /// the original source code body parse result
    pub body: Handle<Array>,
    /// Feedback vector for inline caching (lazily allocated)
    pub feedback_vector: Handle<Array>,

    // Memory Layout:
    // 1. [Value; const_count] - constant pool
    // 2. [u8; inst_size] - bytecode instructions
    data: [u8; 0],
}

impl Code {
    #[must_use]
    pub fn required_layout(consts: usize, inst_bytes: usize) -> Layout {
        let base = Layout::new::<Code>();
        let (with_consts, _) = base
            .extend(Layout::array::<Value>(consts).expect("valid Layout"))
            .expect("valid Layout");
        // Uses u8 for instruction bytes
        let (final_layout, _) = with_consts
            .extend(Layout::array::<u8>(inst_bytes).expect("valid Layout"))
            .expect("valid Layout");
        final_layout
    }

    /// Initialize the raw memory with data.
    pub fn init_with_data(
        &mut self,
        constants: &[Value],
        instructions: &[u8],
        feedback_slot_count: u32,
        body: Handle<Array>,
        feedback_vector: Handle<Array>,
    ) {
        self.header = Header::new_object(ObjectType::Code);
        self.const_count = constants.len() as u32;
        self.inst_size = instructions.len() as u32;
        self.feedback_slot_count = feedback_slot_count;
        self.body = body;
        self.feedback_vector = feedback_vector;

        // SAFETY: this is safe
        unsafe {
            let ptr_base = self.data.as_mut_ptr();

            // Copy Constants
            let ptr_consts = ptr_base as *mut Value;
            ptr::copy_nonoverlapping(
                constants.as_ptr(),
                ptr_consts,
                constants.len(),
            );

            // Copy Instructions
            // Offset by size of constant pool
            let offset_bytes = mem::size_of_val(constants);
            let ptr_insts = ptr_base.add(offset_bytes);

            ptr::copy_nonoverlapping(
                instructions.as_ptr(),
                ptr_insts,
                instructions.len(),
            );
        }
    }

    pub fn constants(&self) -> &[Value] {
        // SAFETY: Constants are stored at the start of data with length const_count,
        // initialized during init_with_data and never modified.
        unsafe {
            let ptr = self.data.as_ptr() as *const Value;
            std::slice::from_raw_parts(ptr, self.const_count as usize)
        }
    }

    pub fn instructions(&self) -> &[u8] {
        // SAFETY: Instructions are stored after constants at offset (const_count * sizeof(Value)),
        // initialized during init_with_data and never modified.
        unsafe {
            let offset_bytes =
                self.const_count as usize * mem::size_of::<Value>();
            let ptr = self.data.as_ptr().add(offset_bytes);
            std::slice::from_raw_parts(ptr, self.inst_size as usize)
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
            self.inst_size as usize,
        )
        .size()
    }
}

impl Visitable for Code {
    fn visit_edges_mut(&mut self, visitor: &mut impl Visitor) {
        // Visit strong references in fields
        visitor.visit_mut(self.body.as_value_mut());

        // feedback_vector may be null (lazily allocated)
        if !self.feedback_vector.as_ptr().is_null() {
            visitor.visit_mut(self.feedback_vector.as_value_mut());
        }

        // Visit constants
        let count = self.const_count as usize;
        let ptr = self.data.as_mut_ptr() as *mut Value;
        // SAFETY: this is safe by contract
        let constants = unsafe { std::slice::from_raw_parts_mut(ptr, count) };
        for val in constants.iter_mut() {
            visitor.visit_mut(val);
        }
    }

    fn visit_edges(&self, visitor: &impl Visitor) {
        visitor.visit(self.body.as_value_ref());

        // feedback_vector may be null (lazily allocated)
        if !self.feedback_vector.as_ptr().is_null() {
            visitor.visit(self.feedback_vector.as_value_ref());
        }

        for val in self.constants() {
            visitor.visit(val);
        }
    }
}

/// Helper to write bytecode into a buffer
#[derive(Default)]
pub struct BytecodeWriter {
    buffer: Vec<u8>,
}

impl BytecodeWriter {
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    #[allow(dead_code)]
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.buffer.is_empty()
    }

    pub fn emit_op(&mut self, op: OpCode) {
        self.buffer.push(op as u8);
    }

    #[allow(dead_code)]
    pub fn emit_u8(&mut self, val: u8) {
        self.buffer.push(val);
    }

    pub fn emit_u16(&mut self, val: u16) {
        self.buffer.extend_from_slice(&val.to_ne_bytes());
    }

    pub fn emit_i32(&mut self, val: i32) {
        self.buffer.extend_from_slice(&val.to_ne_bytes());
    }

    #[must_use]
    pub fn into_inner(self) -> Vec<u8> {
        self.buffer
    }

    #[allow(dead_code)]
    #[must_use]
    pub fn len(&self) -> usize {
        self.buffer.len()
    }

    /// Pushes a value from the constant pool.
    pub fn emit_push_constant(&mut self, index: u16) {
        self.emit_op(OpCode::PushConstant);
        self.emit_u16(index);
    }

    /// Pushes the receiver (self) onto the stack.
    pub fn emit_push_self(&mut self) {
        self.emit_op(OpCode::PushSelf);
    }

    /// Push Small Integer
    pub fn emit_push_small_integer(&mut self, value: i32) {
        self.emit_op(OpCode::PushSmallInteger);
        self.emit_i32(value);
    }

    /// Sends a message.
    pub fn emit_send(&mut self, selector_index: u16, feedback_index: u16) {
        self.emit_op(OpCode::Send);
        self.emit_u16(selector_index);
        self.emit_u16(feedback_index);
    }

    /// Send a primitive message
    pub fn emit_send_primitive(&mut self, primitive_index: u16) {
        self.emit_op(OpCode::SendPrimitive);
        self.emit_u16(primitive_index);
    }

    /// Send to any super
    pub fn emit_send_super(
        &mut self,
        selector_index: u16,
        feedback_index: u16,
    ) {
        self.emit_op(OpCode::SendSuper);
        self.emit_u16(selector_index);
        self.emit_u16(feedback_index);
    }

    /// send to a specific parent
    pub fn emit_send_parent(
        &mut self,
        parent_name_index: u16,
        selector_index: u16,
        feedback_index: u16,
    ) {
        self.emit_op(OpCode::SendParent);
        self.emit_u16(parent_name_index);
        self.emit_u16(selector_index);
        self.emit_u16(feedback_index);
    }

    /// Creates a slot object from a map.
    pub fn emit_create_slot_object(&mut self, map_index: u16) {
        self.emit_op(OpCode::CreateSlotObject);
        self.emit_u16(map_index);
    }

    /// Creates a quotation object from a map
    pub fn emit_create_quotation(&mut self, map_index: u16) {
        self.emit_op(OpCode::CreateQuotation);
        self.emit_u16(map_index);
    }

    /// Move top of stack to return stack
    pub fn emit_push_return(&mut self) {
        self.emit_op(OpCode::PushReturn);
    }

    /// Move top of return stack to stack
    pub fn emit_pop_return(&mut self) {
        self.emit_op(OpCode::PopReturn);
    }

    /// Returns from the current activation.
    pub fn emit_return(&mut self) {
        self.emit_op(OpCode::Return);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_writer_primitives() {
        let mut writer = BytecodeWriter::new();
        writer.emit_u8(0x12);
        writer.emit_u16(0x3456);
        writer.emit_i32(0x789ABCDE);

        let bytes = writer.into_inner();

        let expected_u8 = 0x12;
        let expected_u16 = 0x3456u16.to_ne_bytes();
        let expected_i32 = 0x789ABCDEi32.to_ne_bytes();

        let mut expected = vec![expected_u8];
        expected.extend_from_slice(&expected_u16);
        expected.extend_from_slice(&expected_i32);

        assert_eq!(bytes, expected);
    }

    #[test]
    fn test_writer_opcodes() {
        let mut writer = BytecodeWriter::new();
        writer.emit_op(OpCode::Return);
        writer.emit_op(OpCode::Send);

        let bytes = writer.into_inner();
        assert_eq!(bytes, vec![0x00, 0x04]);
    }

    #[test]
    fn test_decoding_scenario() {
        // Construct a sequence manually
        let mut writer = BytecodeWriter::new();

        // PushSmallInteger 100
        writer.emit_op(OpCode::PushSmallInteger);
        writer.emit_i32(100);

        // Send (Selector 1, Feedback 2)
        writer.emit_op(OpCode::Send);
        writer.emit_u16(1);
        writer.emit_u16(2);

        // Return
        writer.emit_op(OpCode::Return);

        let bytes = writer.into_inner();
        let mut cursor = 0;

        // Helper to read types
        let read_u8 = |cursor: &mut usize, bytes: &[u8]| -> u8 {
            let val = bytes[*cursor];
            *cursor += 1;
            val
        };

        let read_i32 = |cursor: &mut usize, bytes: &[u8]| -> i32 {
            let slice = &bytes[*cursor..*cursor + 4];
            let val = i32::from_ne_bytes(slice.try_into().unwrap());
            *cursor += 4;
            val
        };

        let read_u16 = |cursor: &mut usize, bytes: &[u8]| -> u16 {
            let slice = &bytes[*cursor..*cursor + 2];
            let val = u16::from_ne_bytes(slice.try_into().unwrap());
            *cursor += 2;
            val
        };

        // Decode
        // 1. PushSmallInteger
        let op = OpCode::from_u8(read_u8(&mut cursor, &bytes));
        assert_eq!(op, OpCode::PushSmallInteger);
        let val = read_i32(&mut cursor, &bytes);
        assert_eq!(val, 100);

        // 2. Send
        let op = OpCode::from_u8(read_u8(&mut cursor, &bytes));
        assert_eq!(op, OpCode::Send);
        let sel = read_u16(&mut cursor, &bytes);
        assert_eq!(sel, 1);
        let fb = read_u16(&mut cursor, &bytes);
        assert_eq!(fb, 2);

        // 3. Return
        let op = OpCode::from_u8(read_u8(&mut cursor, &bytes));
        assert_eq!(op, OpCode::Return);

        assert_eq!(cursor, bytes.len());
    }
}
