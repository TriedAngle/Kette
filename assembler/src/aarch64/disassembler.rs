use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DisasmError {
    UnexpectedEof { offset: usize },
    UnsupportedInstruction { offset: usize, insn: u32 },
    InvalidRelativeTarget { offset: usize, target: i64 },
}

impl fmt::Display for DisasmError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnexpectedEof { offset } => {
                write!(f, "unexpected EOF at byte offset {offset}")
            }
            Self::UnsupportedInstruction { offset, insn } => {
                write!(
                    f,
                    "unsupported instruction 0x{insn:08x} at byte offset {offset}"
                )
            }
            Self::InvalidRelativeTarget { offset, target } => {
                write!(
                    f,
                    "invalid relative target {target} at byte offset {offset}"
                )
            }
        }
    }
}

impl std::error::Error for DisasmError {}

pub struct DisasmOptions<'a> {
    pub symbol_resolver: Option<&'a dyn Fn(usize) -> Option<String>>,
}

impl<'a> Default for DisasmOptions<'a> {
    fn default() -> Self {
        Self {
            symbol_resolver: None,
        }
    }
}

pub fn disassemble(bytes: &[u8]) -> Result<String, DisasmError> {
    disassemble_with_options(bytes, &DisasmOptions::default())
}

pub fn disassemble_with_options(
    bytes: &[u8],
    options: &DisasmOptions<'_>,
) -> Result<String, DisasmError> {
    let auto_labels = if options.symbol_resolver.is_none() {
        Some(collect_auto_labels(bytes)?)
    } else {
        None
    };

    let mut out = Vec::new();
    let mut pc = 0usize;
    while pc < bytes.len() {
        let inst_start = pc;
        if let Some(labels) = &auto_labels {
            if let Some(name) = labels.get(&inst_start) {
                out.push(format!("{name}:"));
            }
        }

        let insn = read_u32(bytes, &mut pc)?;
        let text = if (insn & 0xFFFF_FC1F) == 0xD65F_0000 {
            let rn = ((insn >> 5) & 0x1F) as usize;
            format!("ret {}", reg_name(rn))
        } else if (insn & 0xFC00_0000) == 0x1400_0000 {
            let imm26 = sign_extend(insn & 0x03FF_FFFF, 26);
            let target = relative_target(inst_start, imm26 << 2, inst_start)?;
            format!(
                "b {}",
                format_target(
                    target,
                    options.symbol_resolver,
                    auto_labels.as_ref()
                )
            )
        } else if (insn & 0xFC00_0000) == 0x9400_0000 {
            let imm26 = sign_extend(insn & 0x03FF_FFFF, 26);
            let target = relative_target(inst_start, imm26 << 2, inst_start)?;
            format!(
                "bl {}",
                format_target(
                    target,
                    options.symbol_resolver,
                    auto_labels.as_ref()
                )
            )
        } else if (insn & 0xFF00_0010) == 0x5400_0000 {
            let imm19 = sign_extend((insn >> 5) & 0x7F_FFFF, 19);
            let cond = (insn & 0xF) as u8;
            let target = relative_target(inst_start, imm19 << 2, inst_start)?;
            format!(
                "b.{} {}",
                cond_name(cond),
                format_target(
                    target,
                    options.symbol_resolver,
                    auto_labels.as_ref()
                )
            )
        } else if (insn & 0xFFE0_FC00) == 0xAA00_03E0 {
            let rm = ((insn >> 16) & 0x1F) as usize;
            let rd = (insn & 0x1F) as usize;
            format!("mov {}, {}", reg_name(rd), reg_name(rm))
        } else if (insn & 0xFFE0_FC00) == 0x8B00_0000 {
            let rm = ((insn >> 16) & 0x1F) as usize;
            let rn = ((insn >> 5) & 0x1F) as usize;
            let rd = (insn & 0x1F) as usize;
            format!("add {}, {}, {}", reg_name(rd), reg_name(rn), reg_name(rm))
        } else if (insn & 0xFFE0_FC00) == 0xCB00_0000 {
            let rm = ((insn >> 16) & 0x1F) as usize;
            let rn = ((insn >> 5) & 0x1F) as usize;
            let rd = (insn & 0x1F) as usize;
            format!("sub {}, {}, {}", reg_name(rd), reg_name(rn), reg_name(rm))
        } else if (insn & 0xFFE0_FC1F) == 0xEB00_001F {
            let rm = ((insn >> 16) & 0x1F) as usize;
            let rn = ((insn >> 5) & 0x1F) as usize;
            format!("cmp {}, {}", reg_name(rn), reg_name(rm))
        } else if (insn & 0xFF00_001F) == 0xF100_001F {
            let rn = ((insn >> 5) & 0x1F) as usize;
            let imm = ((insn >> 10) & 0xFFF) as u32;
            format!("cmp {}, {}", reg_name(rn), imm)
        } else if (insn & 0xFF80_0000) == 0xD280_0000 {
            let hw = (insn >> 21) & 0b11;
            let imm16 = (insn >> 5) & 0xFFFF;
            let rd = (insn & 0x1F) as usize;
            format!("movz {}, {}, lsl #{}", reg_name(rd), imm16, hw * 16)
        } else if (insn & 0xFF80_0000) == 0xF280_0000 {
            let hw = (insn >> 21) & 0b11;
            let imm16 = (insn >> 5) & 0xFFFF;
            let rd = (insn & 0x1F) as usize;
            format!("movk {}, {}, lsl #{}", reg_name(rd), imm16, hw * 16)
        } else if (insn & 0xFFC0_03FF) == 0xD100_03FF {
            let imm = (insn >> 10) & 0xFFF;
            format!("sub sp, sp, {}", imm)
        } else if (insn & 0xFFC0_03FF) == 0x9100_03FF {
            let imm = (insn >> 10) & 0xFFF;
            format!("add sp, sp, {}", imm)
        } else if (insn & 0xFFC0_03E0) == 0xF900_03E0 {
            let imm = ((insn >> 10) & 0xFFF) * 8;
            let rt = (insn & 0x1F) as usize;
            format!("str {}, [sp, #{}]", reg_name(rt), imm)
        } else if (insn & 0xFFC0_03E0) == 0xF940_03E0 {
            let imm = ((insn >> 10) & 0xFFF) * 8;
            let rt = (insn & 0x1F) as usize;
            format!("ldr {}, [sp, #{}]", reg_name(rt), imm)
        } else {
            return Err(DisasmError::UnsupportedInstruction {
                offset: inst_start,
                insn,
            });
        };

        out.push(format!("{inst_start:04x}: {text}"));
    }

    Ok(out.join("\n"))
}

fn collect_auto_labels(
    bytes: &[u8],
) -> Result<BTreeMap<usize, String>, DisasmError> {
    let mut targets = BTreeSet::new();
    let mut pc = 0usize;
    while pc < bytes.len() {
        let inst_start = pc;
        let insn = read_u32(bytes, &mut pc)?;
        if (insn & 0xFC00_0000) == 0x1400_0000
            || (insn & 0xFC00_0000) == 0x9400_0000
        {
            let imm26 = sign_extend(insn & 0x03FF_FFFF, 26);
            targets.insert(relative_target(
                inst_start,
                imm26 << 2,
                inst_start,
            )?);
        } else if (insn & 0xFF00_0010) == 0x5400_0000 {
            let imm19 = sign_extend((insn >> 5) & 0x7F_FFFF, 19);
            targets.insert(relative_target(
                inst_start,
                imm19 << 2,
                inst_start,
            )?);
        }
    }

    let mut labels = BTreeMap::new();
    for (idx, target) in targets.into_iter().enumerate() {
        labels.insert(target, format!("L{idx}"));
    }
    Ok(labels)
}

fn read_u32(bytes: &[u8], pc: &mut usize) -> Result<u32, DisasmError> {
    if bytes.len().saturating_sub(*pc) < 4 {
        return Err(DisasmError::UnexpectedEof { offset: *pc });
    }
    let v = u32::from_le_bytes(bytes[*pc..*pc + 4].try_into().expect("slice"));
    *pc += 4;
    Ok(v)
}

fn relative_target(
    branch_pc: usize,
    disp_bytes: i64,
    offset: usize,
) -> Result<usize, DisasmError> {
    let target = branch_pc as i64 + disp_bytes;
    if target < 0 {
        return Err(DisasmError::InvalidRelativeTarget { offset, target });
    }
    Ok(target as usize)
}

fn sign_extend(v: u32, bits: u32) -> i64 {
    let shift = 64 - bits;
    ((v as i64) << shift) >> shift
}

fn format_target(
    target: usize,
    resolver: Option<&dyn Fn(usize) -> Option<String>>,
    auto_labels: Option<&BTreeMap<usize, String>>,
) -> String {
    if let Some(resolve) = resolver {
        if let Some(name) = resolve(target) {
            return name;
        }
    }
    if let Some(labels) = auto_labels {
        if let Some(name) = labels.get(&target) {
            return name.clone();
        }
    }
    format!("0x{target:04x}")
}

fn cond_name(cond: u8) -> &'static str {
    match cond {
        0x0 => "eq",
        0x1 => "ne",
        0x2 => "cs",
        0x3 => "cc",
        0x4 => "mi",
        0x5 => "pl",
        0x6 => "vs",
        0x7 => "vc",
        0x8 => "hi",
        0x9 => "ls",
        0xA => "ge",
        0xB => "lt",
        0xC => "gt",
        0xD => "le",
        0xE => "al",
        _ => "nv",
    }
}

fn reg_name(idx: usize) -> &'static str {
    match idx {
        0 => "x0",
        1 => "x1",
        2 => "x2",
        3 => "x3",
        4 => "x4",
        5 => "x5",
        6 => "x6",
        7 => "x7",
        8 => "x8",
        9 => "x9",
        10 => "x10",
        11 => "x11",
        12 => "x12",
        13 => "x13",
        14 => "x14",
        15 => "x15",
        16 => "x16",
        17 => "x17",
        18 => "x18",
        19 => "x19",
        20 => "x20",
        21 => "x21",
        22 => "x22",
        23 => "x23",
        24 => "x24",
        25 => "x25",
        26 => "x26",
        27 => "x27",
        28 => "x28",
        29 => "x29",
        30 => "x30",
        31 => "sp",
        _ => "<bad-reg>",
    }
}
