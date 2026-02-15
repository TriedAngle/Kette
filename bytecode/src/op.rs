/// Bytecode opcodes.
///
/// Register operands are 8-bit by default. The [`Wide`](Op::Wide) prefix
/// promotes register operands to 16-bit. Constant pool indices and feedback
/// indices are always 16-bit. Stack offsets are always 32-bit.
///
/// The [`ExtraWide`](Op::ExtraWide) prefix promotes operands to 32-bit.
/// Currently only used with [`LoadSmi`](Op::LoadSmi).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum Op {
    /// Prefix: the next instruction uses 16-bit register/immediate operands.
    Wide = 0x00,

    /// Prefix: the next instruction uses 32-bit operands.
    /// Currently only valid before [`LoadSmi`](Op::LoadSmi).
    ExtraWide,

    /// Load a constant pool entry into the accumulator.
    /// Operands: `idx:u16`
    LoadConstant,

    /// Load a small integer literal into the accumulator.
    /// Operands: `value:i8` (wide: `i16`, extra-wide: `i32`)
    LoadSmi,

    /// Non-local return. Returns the accumulator up the call chain.
    Return,

    /// Return from the current block. Returns the accumulator.
    LocalReturn,

    /// Create an object from a map and a range of value registers.
    /// Operands: `map_idx:u16`, `values_reg:u8` (wide: `u16`)
    CreateObject,

    /// Create a block (closure) from a constant pool entry.
    /// Operands: `block_idx:u16`
    CreateBlock,

    /// Send a message. Self is expected in `r0`, arguments start at `reg`.
    /// Operands: `message_idx:u16`, `reg:u8` (wide: `u16`), `argc:u8`, `feedback_idx:u16`
    Send,

    /// Load a local register into the accumulator.
    /// Operands: `reg:u8` (wide: `u16`)
    LoadLocal,

    /// Store the accumulator into a local register.
    /// Operands: `reg:u8` (wide: `u16`)
    StoreLocal,

    /// Load from an arbitrary stack offset into the accumulator.
    /// Operands: `offset:u32`
    LoadStack,

    /// Store the accumulator at an arbitrary stack offset.
    /// Operands: `offset:u32`
    StoreStack,

    /// Load from a heap-allocated temp array (Smalltalk-style captured variables).
    /// Operands: `array_idx:u16`, `idx:u16`
    LoadTemp,

    /// Store the accumulator into a heap-allocated temp array.
    /// Operands: `array_idx:u16`, `idx:u16`
    StoreTemp,

    /// Load from an associative global slot (avoids global name lookup).
    /// Operands: `idx:u16`
    LoadAssoc,

    /// Store the accumulator into an associative global slot.
    /// Operands: `idx:u16`
    StoreAssoc,

    /// Move between local registers (does not touch the accumulator).
    /// Operands: `dst:u8` (wide: `u16`), `src:u8` (wide: `u16`)
    Mov,

    /// Move from a local register to an arbitrary stack slot.
    /// Operands: `offset:u32`, `src:u8` (wide: `u16`)
    MovToStack,

    /// Move from an arbitrary stack slot to a local register.
    /// Operands: `dst:u8` (wide: `u16`), `offset:u32`
    MovFromStack,

    /// Move from a local register into a heap-allocated temp array.
    /// Operands: `array_idx:u16`, `idx:u16`, `src:u8` (wide: `u16`)
    MovToTemp,

    /// Move from a heap-allocated temp array into a local register.
    /// Operands: `dst:u8` (wide: `u16`), `array_idx:u16`, `idx:u16`
    MovFromTemp,

    /// Move from a local register into an associative global slot.
    /// Operands: `idx:u16`, `src:u8` (wide: `u16`)
    MovToAssoc,

    /// Move from an associative global slot into a local register.
    /// Operands: `dst:u8` (wide: `u16`), `idx:u16`
    MovFromAssoc,

    /// Unconditional relative jump.
    /// Operands: `offset:i16` (relative to end of instruction)
    Jump,

    /// Jump if the accumulator is truthy.
    /// Operands: `offset:i16`
    JumpIfTrue,

    /// Jump if the accumulator is falsy.
    /// Operands: `offset:i16`
    JumpIfFalse,

    /// Resend a message to the parent. Same operands as [`Send`](Op::Send).
    /// Operands: `message_idx:u16`, `reg:u8` (wide: `u16`), `argc:u8`, `feedback_idx:u16`
    Resend,

    /// Directed resend: resend via a named parent slot.
    /// Operands: `message_idx:u16`, `reg:u8` (wide: `u16`), `argc:u8`, `feedback_idx:u16`, `delegate_idx:u16`
    DirectedResend,
}

impl Op {
    pub const COUNT: usize = Op::DirectedResend as usize + 1;

    /// Convert a raw byte to an opcode without a bounds check.
    ///
    /// # Safety
    ///
    /// `byte` must be a valid opcode value (`< Op::COUNT`).
    #[inline(always)]
    pub unsafe fn from_u8_unchecked(byte: u8) -> Self {
        debug_assert!(
            (byte as usize) < Self::COUNT,
            "invalid opcode: 0x{byte:02x}"
        );
        core::mem::transmute::<u8, Op>(byte)
    }

    /// Whether this opcode has operands affected by the `Wide` or `ExtraWide`
    /// prefix.
    pub const fn has_scalable_operands(self) -> bool {
        matches!(
            self,
            Op::LoadSmi
                | Op::CreateObject
                | Op::Send
                | Op::LoadLocal
                | Op::StoreLocal
                | Op::Mov
                | Op::MovToStack
                | Op::MovFromStack
                | Op::MovToTemp
                | Op::MovFromTemp
                | Op::MovToAssoc
                | Op::MovFromAssoc
                | Op::Resend
                | Op::DirectedResend
        )
    }
}

impl TryFrom<u8> for Op {
    type Error = u8;

    fn try_from(byte: u8) -> Result<Self, u8> {
        if byte < Self::COUNT as u8 {
            // SAFETY: Op is repr(u8) with contiguous variants starting at 0.
            Ok(unsafe { core::mem::transmute::<u8, Op>(byte) })
        } else {
            Err(byte)
        }
    }
}
