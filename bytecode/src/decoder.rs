use crate::instruction::Instruction;
use crate::op::Op;

/// Operand width selected by an optional prefix byte.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
enum Width {
    Normal = 0,
    Wide = 1,
    ExtraWide = 2,
}

/// Decodes a bytecode byte slice into [`Instruction`]s.
///
/// # Safety contract
///
/// The bytecode **must** be well-formed (as produced by [`BytecodeBuilder`]).
/// In debug builds, malformed bytecode triggers a panic via `debug_assert!`.
/// In release builds, malformed bytecode is **undefined behaviour**.
///
/// [`BytecodeBuilder`]: crate::BytecodeBuilder
pub struct BytecodeDecoder<'a> {
    bytes: &'a [u8],
    pos: usize,
}

impl<'a> BytecodeDecoder<'a> {
    pub fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, pos: 0 }
    }

    /// Current byte offset in the stream.
    #[inline(always)]
    pub fn offset(&self) -> usize {
        self.pos
    }

    /// Whether the decoder has reached the end of the bytecode.
    #[inline(always)]
    pub fn is_at_end(&self) -> bool {
        self.pos >= self.bytes.len()
    }

    /// Decode the next instruction, or `None` at end-of-stream.
    ///
    /// See the [struct-level safety docs](BytecodeDecoder) — the bytecode
    /// must be well-formed.
    #[inline(always)]
    pub fn decode_next(&mut self) -> Option<Instruction> {
        if self.is_at_end() {
            return None;
        }
        Some(unsafe { self.decode() })
    }

    /// # Safety
    ///
    /// At least one byte must remain, and the remaining bytes must form a
    /// valid instruction (possibly prefixed).
    #[inline(always)]
    unsafe fn decode(&mut self) -> Instruction {
        let byte = self.read_u8();
        let op = Op::from_u8_unchecked(byte);

        match op {
            Op::Wide => {
                let next = Op::from_u8_unchecked(self.read_u8());
                self.decode_op(next, Width::Wide)
            }
            Op::ExtraWide => {
                let next = Op::from_u8_unchecked(self.read_u8());
                debug_assert!(
                    next == Op::LoadSmi,
                    "ExtraWide only valid before LoadSmi, got {next:?}"
                );
                self.decode_op(next, Width::ExtraWide)
            }
            _ => self.decode_op(op, Width::Normal),
        }
    }

    #[inline(always)]
    unsafe fn decode_op(&mut self, op: Op, width: Width) -> Instruction {
        let wide = width as u8 >= Width::Wide as u8;

        match op {
            Op::Wide | Op::ExtraWide => {
                // SAFETY: we already consumed the prefix in `decode` and
                // dispatched to the real opcode — this arm is unreachable.
                unsafe { std::hint::unreachable_unchecked() }
            }

            Op::LoadConstant => {
                let idx = self.read_u16();
                Instruction::LoadConstant { idx }
            }

            Op::LoadSmi => {
                let value = match width {
                    Width::Normal => self.read_u8() as i8 as i32,
                    Width::Wide => self.read_i16() as i32,
                    Width::ExtraWide => self.read_i32(),
                };
                Instruction::LoadSmi { value }
            }

            Op::Return => Instruction::Return,
            Op::LocalReturn => Instruction::LocalReturn,

            Op::CreateObject => {
                let map_idx = self.read_u16();
                let values_reg = self.read_reg(wide);
                Instruction::CreateObject { map_idx, values_reg }
            }

            Op::CreateBlock => {
                let block_idx = self.read_u16();
                Instruction::CreateBlock { block_idx }
            }

            Op::Send => {
                let message_idx = self.read_u16();
                let reg = self.read_reg(wide);
                let argc = self.read_u8();
                let feedback_idx = self.read_u16();
                Instruction::Send { message_idx, reg, argc, feedback_idx }
            }

            Op::LoadLocal => Instruction::LoadLocal { reg: self.read_reg(wide) },
            Op::StoreLocal => Instruction::StoreLocal { reg: self.read_reg(wide) },

            Op::LoadStack => Instruction::LoadStack { offset: self.read_u32() },
            Op::StoreStack => Instruction::StoreStack { offset: self.read_u32() },

            Op::LoadTemp => {
                let array_idx = self.read_u16();
                let idx = self.read_u16();
                Instruction::LoadTemp { array_idx, idx }
            }

            Op::StoreTemp => {
                let array_idx = self.read_u16();
                let idx = self.read_u16();
                Instruction::StoreTemp { array_idx, idx }
            }

            Op::LoadAssoc => Instruction::LoadAssoc { idx: self.read_u16() },
            Op::StoreAssoc => Instruction::StoreAssoc { idx: self.read_u16() },

            Op::Mov => {
                let dst = self.read_reg(wide);
                let src = self.read_reg(wide);
                Instruction::Mov { dst, src }
            }

            Op::MovToStack => {
                let offset = self.read_u32();
                let src = self.read_reg(wide);
                Instruction::MovToStack { offset, src }
            }

            Op::MovFromStack => {
                let dst = self.read_reg(wide);
                let offset = self.read_u32();
                Instruction::MovFromStack { dst, offset }
            }

            Op::MovToTemp => {
                let array_idx = self.read_u16();
                let idx = self.read_u16();
                let src = self.read_reg(wide);
                Instruction::MovToTemp { array_idx, idx, src }
            }

            Op::MovFromTemp => {
                let dst = self.read_reg(wide);
                let array_idx = self.read_u16();
                let idx = self.read_u16();
                Instruction::MovFromTemp { dst, array_idx, idx }
            }

            Op::MovToAssoc => {
                let idx = self.read_u16();
                let src = self.read_reg(wide);
                Instruction::MovToAssoc { idx, src }
            }

            Op::MovFromAssoc => {
                let dst = self.read_reg(wide);
                let idx = self.read_u16();
                Instruction::MovFromAssoc { dst, idx }
            }

            Op::Jump => Instruction::Jump { offset: self.read_i16() },
            Op::JumpIfTrue => Instruction::JumpIfTrue { offset: self.read_i16() },
            Op::JumpIfFalse => Instruction::JumpIfFalse { offset: self.read_i16() },

            Op::Resend => {
                let message_idx = self.read_u16();
                let reg = self.read_reg(wide);
                let argc = self.read_u8();
                let feedback_idx = self.read_u16();
                Instruction::Resend { message_idx, reg, argc, feedback_idx }
            }

            Op::DirectedResend => {
                let message_idx = self.read_u16();
                let reg = self.read_reg(wide);
                let argc = self.read_u8();
                let feedback_idx = self.read_u16();
                let delegate_idx = self.read_u16();
                Instruction::DirectedResend { message_idx, reg, argc, feedback_idx, delegate_idx }
            }
        }
    }

    #[inline(always)]
    unsafe fn read_u8(&mut self) -> u8 {
        debug_assert!(self.pos < self.bytes.len(), "read_u8 out of bounds");
        let v = *self.bytes.get_unchecked(self.pos);
        self.pos += 1;
        v
    }

    #[inline(always)]
    unsafe fn read_u16(&mut self) -> u16 {
        debug_assert!(self.pos + 2 <= self.bytes.len(), "read_u16 out of bounds");
        let ptr = self.bytes.as_ptr().add(self.pos) as *const u16;
        let v = u16::from_le(ptr.read_unaligned());
        self.pos += 2;
        v
    }

    #[inline(always)]
    unsafe fn read_i16(&mut self) -> i16 {
        self.read_u16() as i16
    }

    #[inline(always)]
    unsafe fn read_u32(&mut self) -> u32 {
        debug_assert!(self.pos + 4 <= self.bytes.len(), "read_u32 out of bounds");
        let ptr = self.bytes.as_ptr().add(self.pos) as *const u32;
        let v = u32::from_le(ptr.read_unaligned());
        self.pos += 4;
        v
    }

    #[inline(always)]
    unsafe fn read_i32(&mut self) -> i32 {
        self.read_u32() as i32
    }

    #[inline(always)]
    unsafe fn read_reg(&mut self, wide: bool) -> u16 {
        if wide {
            self.read_u16()
        } else {
            self.read_u8() as u16
        }
    }
}

impl<'a> Iterator for BytecodeDecoder<'a> {
    type Item = Instruction;

    #[inline(always)]
    fn next(&mut self) -> Option<Instruction> {
        self.decode_next()
    }
}
