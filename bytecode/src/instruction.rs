use core::fmt;

/// A decoded instruction with all operands resolved to their widest types.
///
/// Register operands are always `u16` regardless of whether the instruction
/// was encoded in narrow or wide form.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Instruction {
    LoadConstant {
        idx: u16,
    },
    LoadSmi {
        value: i32,
    },
    Return,
    LocalReturn,
    CreateObject {
        map_idx: u16,
        values_reg: u16,
    },
    CreateBlock {
        block_idx: u16,
    },
    Send {
        message_idx: u16,
        reg: u16,
        argc: u8,
        feedback_idx: u16,
    },
    LoadLocal {
        reg: u16,
    },
    StoreLocal {
        reg: u16,
    },
    LoadStack {
        offset: u32,
    },
    StoreStack {
        offset: u32,
    },
    LoadTemp {
        array_idx: u16,
        idx: u16,
    },
    StoreTemp {
        array_idx: u16,
        idx: u16,
    },
    LoadAssoc {
        idx: u16,
    },
    StoreAssoc {
        idx: u16,
    },
    Mov {
        dst: u16,
        src: u16,
    },
    MovToStack {
        offset: u32,
        src: u16,
    },
    MovFromStack {
        dst: u16,
        offset: u32,
    },
    MovToTemp {
        array_idx: u16,
        idx: u16,
        src: u16,
    },
    MovFromTemp {
        dst: u16,
        array_idx: u16,
        idx: u16,
    },
    MovToAssoc {
        idx: u16,
        src: u16,
    },
    MovFromAssoc {
        dst: u16,
        idx: u16,
    },
    Jump {
        offset: i16,
    },
    JumpIfTrue {
        offset: i16,
    },
    JumpIfFalse {
        offset: i16,
    },
    Resend {
        message_idx: u16,
        reg: u16,
        argc: u8,
        feedback_idx: u16,
    },
    DirectedResend {
        message_idx: u16,
        reg: u16,
        argc: u8,
        feedback_idx: u16,
        delegate_idx: u16,
    },
}

impl fmt::Display for Instruction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::LoadConstant { idx } => write!(f, "LoadConstant #{idx}"),
            Self::LoadSmi { value } => write!(f, "LoadSmi {value}"),
            Self::Return => write!(f, "Return"),
            Self::LocalReturn => write!(f, "LocalReturn"),
            Self::CreateObject {
                map_idx,
                values_reg,
            } => {
                write!(f, "CreateObject #{map_idx} r{values_reg}")
            }
            Self::CreateBlock { block_idx } => {
                write!(f, "CreateBlock #{block_idx}")
            }
            Self::Send {
                message_idx,
                reg,
                argc,
                feedback_idx,
            } => {
                write!(f, "Send #{message_idx} r{reg} {argc} ~{feedback_idx}")
            }
            Self::LoadLocal { reg } => write!(f, "LoadLocal r{reg}"),
            Self::StoreLocal { reg } => write!(f, "StoreLocal r{reg}"),
            Self::LoadStack { offset } => write!(f, "LoadStack @{offset}"),
            Self::StoreStack { offset } => write!(f, "StoreStack @{offset}"),
            Self::LoadTemp { array_idx, idx } => {
                write!(f, "LoadTemp #{array_idx}[{idx}]")
            }
            Self::StoreTemp { array_idx, idx } => {
                write!(f, "StoreTemp #{array_idx}[{idx}]")
            }
            Self::LoadAssoc { idx } => write!(f, "LoadAssoc #{idx}"),
            Self::StoreAssoc { idx } => write!(f, "StoreAssoc #{idx}"),
            Self::Mov { dst, src } => write!(f, "Mov r{dst}, r{src}"),
            Self::MovToStack { offset, src } => {
                write!(f, "MovToStack @{offset}, r{src}")
            }
            Self::MovFromStack { dst, offset } => {
                write!(f, "MovFromStack r{dst}, @{offset}")
            }
            Self::MovToTemp {
                array_idx,
                idx,
                src,
            } => {
                write!(f, "MovToTemp #{array_idx}[{idx}], r{src}")
            }
            Self::MovFromTemp {
                dst,
                array_idx,
                idx,
            } => {
                write!(f, "MovFromTemp r{dst}, #{array_idx}[{idx}]")
            }
            Self::MovToAssoc { idx, src } => {
                write!(f, "MovToAssoc #{idx}, r{src}")
            }
            Self::MovFromAssoc { dst, idx } => {
                write!(f, "MovFromAssoc r{dst}, #{idx}")
            }
            Self::Jump { offset } => write!(f, "Jump {offset:+}"),
            Self::JumpIfTrue { offset } => write!(f, "JumpIfTrue {offset:+}"),
            Self::JumpIfFalse { offset } => write!(f, "JumpIfFalse {offset:+}"),
            Self::Resend {
                message_idx,
                reg,
                argc,
                feedback_idx,
            } => {
                write!(f, "Resend #{message_idx} r{reg} {argc} ~{feedback_idx}")
            }
            Self::DirectedResend {
                message_idx,
                reg,
                argc,
                feedback_idx,
                delegate_idx,
            } => {
                write!(f, "DirectedResend #{message_idx} r{reg} {argc} ~{feedback_idx} #{delegate_idx}")
            }
        }
    }
}
