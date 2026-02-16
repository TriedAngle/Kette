use crate::op::Op;

/// A forward jump whose offset has not yet been resolved.
///
/// Created by [`BytecodeBuilder::jump`], [`BytecodeBuilder::jump_if_true`],
/// and [`BytecodeBuilder::jump_if_false`]. Resolve it with
/// [`BytecodeBuilder::bind`].
#[derive(Debug)]
pub struct Label {
    /// Position of the i16 offset bytes in the buffer.
    offset_pos: usize,
    /// Position right after the jump instruction (base for relative offset).
    base: usize,
}

/// Builds a bytecode byte sequence.
///
/// The builder automatically emits the [`Op::Wide`] prefix when a register
/// operand exceeds `u8::MAX`.
pub struct BytecodeBuilder {
    buf: Vec<u8>,
}

impl BytecodeBuilder {
    pub fn new() -> Self {
        Self { buf: Vec::new() }
    }

    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            buf: Vec::with_capacity(capacity),
        }
    }

    /// Current byte offset in the bytecode stream.
    pub fn current_offset(&self) -> usize {
        self.buf.len()
    }

    pub fn into_bytes(self) -> Vec<u8> {
        self.buf
    }

    pub fn as_bytes(&self) -> &[u8] {
        &self.buf
    }

    // ── emit helpers ───────────────────────────────────────────────

    fn emit_u8(&mut self, v: u8) {
        self.buf.push(v);
    }

    fn emit_u16(&mut self, v: u16) {
        self.buf.extend_from_slice(&v.to_le_bytes());
    }

    fn emit_i16(&mut self, v: i16) {
        self.buf.extend_from_slice(&v.to_le_bytes());
    }

    fn emit_u32(&mut self, v: u32) {
        self.buf.extend_from_slice(&v.to_le_bytes());
    }

    fn emit_op(&mut self, op: Op) {
        self.buf.push(op as u8);
    }

    /// Returns `true` if the register needed the wide encoding.
    fn needs_wide(reg: u16) -> bool {
        reg > u8::MAX as u16
    }

    fn emit_reg(&mut self, reg: u16, wide: bool) {
        if wide {
            self.emit_u16(reg);
        } else {
            self.emit_u8(reg as u8);
        }
    }

    /// `LoadConstant <idx:u16>` — load from constant pool into accumulator.
    pub fn load_constant(&mut self, idx: u16) {
        self.emit_op(Op::LoadConstant);
        self.emit_u16(idx);
    }

    /// `LoadSmi <value>` — load a small integer into the accumulator.
    ///
    /// Automatically selects 8-bit, 16-bit (`Wide`), or 32-bit (`ExtraWide`)
    /// encoding based on the value.
    pub fn load_smi(&mut self, value: i32) {
        if let Ok(v) = i8::try_from(value) {
            self.emit_op(Op::LoadSmi);
            self.emit_u8(v as u8);
        } else if let Ok(v) = i16::try_from(value) {
            self.emit_op(Op::Wide);
            self.emit_op(Op::LoadSmi);
            self.emit_i16(v);
        } else {
            self.emit_op(Op::ExtraWide);
            self.emit_op(Op::LoadSmi);
            self.emit_u32(value as u32);
        }
    }

    /// `Return` — non-local return.
    pub fn return_(&mut self) {
        self.emit_op(Op::Return);
    }

    /// `LocalReturn` — return from current block.
    pub fn local_return(&mut self) {
        self.emit_op(Op::LocalReturn);
    }

    /// `CreateObject <map_idx:u16> <values_reg>` — create an object.
    pub fn create_object(&mut self, map_idx: u16, values_reg: u16) {
        let wide = Self::needs_wide(values_reg);
        if wide {
            self.emit_op(Op::Wide);
        }
        self.emit_op(Op::CreateObject);
        self.emit_u16(map_idx);
        self.emit_reg(values_reg, wide);
    }

    /// `CreateBlock <block_idx:u16>` — create a block/closure.
    pub fn create_block(&mut self, block_idx: u16) {
        self.emit_op(Op::CreateBlock);
        self.emit_u16(block_idx);
    }

    /// `Send <message_idx:u16> <reg> <argc:u8> <feedback_idx:u16>`.
    ///
    /// Self is expected in `r0`, arguments in `reg..reg+argc`.
    pub fn send(
        &mut self,
        message_idx: u16,
        reg: u16,
        argc: u8,
        feedback_idx: u16,
    ) {
        let wide = Self::needs_wide(reg);
        if wide {
            self.emit_op(Op::Wide);
        }
        self.emit_op(Op::Send);
        self.emit_u16(message_idx);
        self.emit_reg(reg, wide);
        self.emit_u8(argc);
        self.emit_u16(feedback_idx);
    }

    /// `Resend <message_idx:u16> <reg> <argc:u8> <feedback_idx:u16>`.
    ///
    /// Resend to parent. Same layout as [`send`](Self::send).
    pub fn resend(
        &mut self,
        message_idx: u16,
        reg: u16,
        argc: u8,
        feedback_idx: u16,
    ) {
        let wide = Self::needs_wide(reg);
        if wide {
            self.emit_op(Op::Wide);
        }
        self.emit_op(Op::Resend);
        self.emit_u16(message_idx);
        self.emit_reg(reg, wide);
        self.emit_u8(argc);
        self.emit_u16(feedback_idx);
    }

    /// `DirectedResend <message_idx:u16> <reg> <argc:u8> <feedback_idx:u16> <delegate_idx:u16>`.
    ///
    /// Directed resend via a named parent slot.
    pub fn directed_resend(
        &mut self,
        message_idx: u16,
        reg: u16,
        argc: u8,
        feedback_idx: u16,
        delegate_idx: u16,
    ) {
        let wide = Self::needs_wide(reg);
        if wide {
            self.emit_op(Op::Wide);
        }
        self.emit_op(Op::DirectedResend);
        self.emit_u16(message_idx);
        self.emit_reg(reg, wide);
        self.emit_u8(argc);
        self.emit_u16(feedback_idx);
        self.emit_u16(delegate_idx);
    }

    /// `LoadLocal <reg>` — load local register into accumulator.
    pub fn load_local(&mut self, reg: u16) {
        let wide = Self::needs_wide(reg);
        if wide {
            self.emit_op(Op::Wide);
        }
        self.emit_op(Op::LoadLocal);
        self.emit_reg(reg, wide);
    }

    /// `StoreLocal <reg>` — store accumulator into local register.
    pub fn store_local(&mut self, reg: u16) {
        let wide = Self::needs_wide(reg);
        if wide {
            self.emit_op(Op::Wide);
        }
        self.emit_op(Op::StoreLocal);
        self.emit_reg(reg, wide);
    }

    /// `LoadStack <offset:u32>` — load from arbitrary stack offset.
    pub fn load_stack(&mut self, offset: u32) {
        self.emit_op(Op::LoadStack);
        self.emit_u32(offset);
    }

    /// `StoreStack <offset:u32>` — store accumulator at arbitrary stack offset.
    pub fn store_stack(&mut self, offset: u32) {
        self.emit_op(Op::StoreStack);
        self.emit_u32(offset);
    }

    /// `LoadTemp <array_idx:u16> <idx:u16>` — load from heap-allocated temp array.
    pub fn load_temp(&mut self, array_idx: u16, idx: u16) {
        self.emit_op(Op::LoadTemp);
        self.emit_u16(array_idx);
        self.emit_u16(idx);
    }

    /// `StoreTemp <array_idx:u16> <idx:u16>` — store into heap-allocated temp array.
    pub fn store_temp(&mut self, array_idx: u16, idx: u16) {
        self.emit_op(Op::StoreTemp);
        self.emit_u16(array_idx);
        self.emit_u16(idx);
    }

    /// `LoadAssoc <idx:u16>` — load from associative global slot.
    pub fn load_assoc(&mut self, idx: u16) {
        self.emit_op(Op::LoadAssoc);
        self.emit_u16(idx);
    }

    /// `StoreAssoc <idx:u16>` — store accumulator into associative global slot.
    pub fn store_assoc(&mut self, idx: u16) {
        self.emit_op(Op::StoreAssoc);
        self.emit_u16(idx);
    }

    /// `Mov <dst> <src>` — move between local registers (accumulator untouched).
    pub fn mov(&mut self, dst: u16, src: u16) {
        let wide = Self::needs_wide(dst) || Self::needs_wide(src);
        if wide {
            self.emit_op(Op::Wide);
        }
        self.emit_op(Op::Mov);
        self.emit_reg(dst, wide);
        self.emit_reg(src, wide);
    }

    /// `MovToStack <offset:u32> <src>` — move from register to stack slot.
    pub fn mov_to_stack(&mut self, offset: u32, src: u16) {
        let wide = Self::needs_wide(src);
        if wide {
            self.emit_op(Op::Wide);
        }
        self.emit_op(Op::MovToStack);
        self.emit_u32(offset);
        self.emit_reg(src, wide);
    }

    /// `MovFromStack <dst> <offset:u32>` — move from stack slot to register.
    pub fn mov_from_stack(&mut self, dst: u16, offset: u32) {
        let wide = Self::needs_wide(dst);
        if wide {
            self.emit_op(Op::Wide);
        }
        self.emit_op(Op::MovFromStack);
        self.emit_reg(dst, wide);
        self.emit_u32(offset);
    }

    /// `MovToTemp <array_idx:u16> <idx:u16> <src>` — move from register to temp array.
    pub fn mov_to_temp(&mut self, array_idx: u16, idx: u16, src: u16) {
        let wide = Self::needs_wide(src);
        if wide {
            self.emit_op(Op::Wide);
        }
        self.emit_op(Op::MovToTemp);
        self.emit_u16(array_idx);
        self.emit_u16(idx);
        self.emit_reg(src, wide);
    }

    /// `MovFromTemp <dst> <array_idx:u16> <idx:u16>` — move from temp array to register.
    pub fn mov_from_temp(&mut self, dst: u16, array_idx: u16, idx: u16) {
        let wide = Self::needs_wide(dst);
        if wide {
            self.emit_op(Op::Wide);
        }
        self.emit_op(Op::MovFromTemp);
        self.emit_reg(dst, wide);
        self.emit_u16(array_idx);
        self.emit_u16(idx);
    }

    /// `MovToAssoc <idx:u16> <src>` — move from register to global slot.
    pub fn mov_to_assoc(&mut self, idx: u16, src: u16) {
        let wide = Self::needs_wide(src);
        if wide {
            self.emit_op(Op::Wide);
        }
        self.emit_op(Op::MovToAssoc);
        self.emit_u16(idx);
        self.emit_reg(src, wide);
    }

    /// `MovFromAssoc <dst> <idx:u16>` — move from global slot to register.
    pub fn mov_from_assoc(&mut self, dst: u16, idx: u16) {
        let wide = Self::needs_wide(dst);
        if wide {
            self.emit_op(Op::Wide);
        }
        self.emit_op(Op::MovFromAssoc);
        self.emit_reg(dst, wide);
        self.emit_u16(idx);
    }

    /// Emit an unconditional forward jump. Returns a [`Label`] that must be
    /// resolved later with [`bind`](Self::bind).
    pub fn jump(&mut self) -> Label {
        self.emit_jump_placeholder(Op::Jump)
    }

    /// Emit a conditional forward jump (truthy). Returns a [`Label`].
    pub fn jump_if_true(&mut self) -> Label {
        self.emit_jump_placeholder(Op::JumpIfTrue)
    }

    /// Emit a conditional forward jump (falsy). Returns a [`Label`].
    pub fn jump_if_false(&mut self) -> Label {
        self.emit_jump_placeholder(Op::JumpIfFalse)
    }

    /// Bind a forward jump label to the current position.
    pub fn bind(&mut self, label: Label) {
        let target = self.buf.len();
        let offset = (target as isize - label.base as isize) as i16;
        self.buf[label.offset_pos..label.offset_pos + 2]
            .copy_from_slice(&offset.to_le_bytes());
    }

    /// Emit an unconditional backward jump to `target` (a byte offset obtained
    /// from [`current_offset`](Self::current_offset)).
    pub fn jump_back(&mut self, target: usize) {
        self.emit_op(Op::Jump);
        let base = self.buf.len() + 2;
        let offset = (target as isize - base as isize) as i16;
        self.emit_i16(offset);
    }

    /// Emit a conditional backward jump (truthy) to `target`.
    pub fn jump_back_if_true(&mut self, target: usize) {
        self.emit_op(Op::JumpIfTrue);
        let base = self.buf.len() + 2;
        let offset = (target as isize - base as isize) as i16;
        self.emit_i16(offset);
    }

    /// Emit a conditional backward jump (falsy) to `target`.
    pub fn jump_back_if_false(&mut self, target: usize) {
        self.emit_op(Op::JumpIfFalse);
        let base = self.buf.len() + 2;
        let offset = (target as isize - base as isize) as i16;
        self.emit_i16(offset);
    }

    fn emit_jump_placeholder(&mut self, op: Op) -> Label {
        self.emit_op(op);
        let offset_pos = self.buf.len();
        self.emit_i16(0); // placeholder
        let base = self.buf.len();
        Label { offset_pos, base }
    }
}

impl Default for BytecodeBuilder {
    fn default() -> Self {
        Self::new()
    }
}
