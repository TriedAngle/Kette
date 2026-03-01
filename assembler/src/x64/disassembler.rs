use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DisasmError {
    UnexpectedEof { offset: usize },
    UnsupportedOpcode { offset: usize, opcode: u8 },
    UnsupportedAddressing { offset: usize },
    InvalidRelativeTarget { offset: usize, target: i64 },
}

impl fmt::Display for DisasmError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnexpectedEof { offset } => {
                write!(f, "unexpected EOF at byte offset {offset}")
            }
            Self::UnsupportedOpcode { offset, opcode } => {
                write!(
                    f,
                    "unsupported opcode 0x{opcode:02x} at byte offset {offset}"
                )
            }
            Self::UnsupportedAddressing { offset } => {
                write!(f, "unsupported addressing mode at byte offset {offset}")
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
        let mut rex = Rex::default();

        if matches!(bytes[pc], 0x40..=0x4F) {
            rex = Rex::from_byte(bytes[pc]);
            pc += 1;
            if pc >= bytes.len() {
                return Err(DisasmError::UnexpectedEof { offset: pc });
            }
        }

        let opcode = bytes[pc];
        pc += 1;

        let text = match opcode {
            0xC3 => "ret".to_string(),
            0x50..=0x57 => {
                let reg =
                    reg_name(((opcode - 0x50) | ((rex.b as u8) << 3)) as usize);
                format!("push {reg}")
            }
            0x58..=0x5F => {
                let reg =
                    reg_name(((opcode - 0x58) | ((rex.b as u8) << 3)) as usize);
                format!("pop {reg}")
            }
            0xB8..=0xBF => {
                let reg =
                    reg_name(((opcode - 0xB8) | ((rex.b as u8) << 3)) as usize);
                let imm = read_u64(bytes, &mut pc)? as i64;
                format!("mov {reg}, {imm}")
            }
            0x89 => {
                let modrm = read_u8(bytes, &mut pc)?;
                let (mode, reg, rm) = decode_modrm(modrm);
                if mode != 0b11 {
                    return Err(DisasmError::UnsupportedAddressing {
                        offset: inst_start,
                    });
                }
                let src = reg_name((reg | ((rex.r as u8) << 3)) as usize);
                let dst = reg_name((rm | ((rex.b as u8) << 3)) as usize);
                format!("mov {dst}, {src}")
            }
            0x01 => {
                let modrm = read_u8(bytes, &mut pc)?;
                let (mode, reg, rm) = decode_modrm(modrm);
                if mode != 0b11 {
                    return Err(DisasmError::UnsupportedAddressing {
                        offset: inst_start,
                    });
                }
                let src = reg_name((reg | ((rex.r as u8) << 3)) as usize);
                let dst = reg_name((rm | ((rex.b as u8) << 3)) as usize);
                format!("add {dst}, {src}")
            }
            0x29 => {
                let modrm = read_u8(bytes, &mut pc)?;
                let (mode, reg, rm) = decode_modrm(modrm);
                if mode != 0b11 {
                    return Err(DisasmError::UnsupportedAddressing {
                        offset: inst_start,
                    });
                }
                let src = reg_name((reg | ((rex.r as u8) << 3)) as usize);
                let dst = reg_name((rm | ((rex.b as u8) << 3)) as usize);
                format!("sub {dst}, {src}")
            }
            0x39 => {
                let modrm = read_u8(bytes, &mut pc)?;
                let (mode, reg, rm) = decode_modrm(modrm);
                if mode != 0b11 {
                    return Err(DisasmError::UnsupportedAddressing {
                        offset: inst_start,
                    });
                }
                let rhs = reg_name((reg | ((rex.r as u8) << 3)) as usize);
                let lhs = reg_name((rm | ((rex.b as u8) << 3)) as usize);
                format!("cmp {lhs}, {rhs}")
            }
            0x81 => {
                let modrm = read_u8(bytes, &mut pc)?;
                let (mode, reg_opcode, rm) = decode_modrm(modrm);
                if mode != 0b11 || reg_opcode != 0b111 {
                    return Err(DisasmError::UnsupportedAddressing {
                        offset: inst_start,
                    });
                }
                let reg = reg_name((rm | ((rex.b as u8) << 3)) as usize);
                let imm = read_u32(bytes, &mut pc)? as i32;
                format!("cmp {reg}, {imm}")
            }
            0xE8 => {
                let disp = read_u32(bytes, &mut pc)? as i32;
                let target = relative_target(pc, disp, inst_start)?;
                format!(
                    "call {}",
                    format_target(
                        target,
                        options.symbol_resolver,
                        auto_labels.as_ref()
                    )
                )
            }
            0xE9 => {
                let disp = read_u32(bytes, &mut pc)? as i32;
                let target = relative_target(pc, disp, inst_start)?;
                format!(
                    "jmp {}",
                    format_target(
                        target,
                        options.symbol_resolver,
                        auto_labels.as_ref()
                    )
                )
            }
            0x0F => {
                let ext = read_u8(bytes, &mut pc)?;
                match ext {
                    0x84 => {
                        let disp = read_u32(bytes, &mut pc)? as i32;
                        let target = relative_target(pc, disp, inst_start)?;
                        format!(
                            "je {}",
                            format_target(
                                target,
                                options.symbol_resolver,
                                auto_labels.as_ref()
                            )
                        )
                    }
                    0x85 => {
                        let disp = read_u32(bytes, &mut pc)? as i32;
                        let target = relative_target(pc, disp, inst_start)?;
                        format!(
                            "jne {}",
                            format_target(
                                target,
                                options.symbol_resolver,
                                auto_labels.as_ref()
                            )
                        )
                    }
                    _ => {
                        return Err(DisasmError::UnsupportedOpcode {
                            offset: inst_start,
                            opcode: ext,
                        });
                    }
                }
            }
            _ => {
                return Err(DisasmError::UnsupportedOpcode {
                    offset: inst_start,
                    opcode,
                });
            }
        };

        out.push(format!("{inst_start:04x}: {text}"));
    }

    Ok(out.join("\n"))
}

#[derive(Debug, Clone, Copy, Default)]
struct Rex {
    r: bool,
    b: bool,
}

impl Rex {
    #[inline]
    fn from_byte(byte: u8) -> Self {
        Self {
            r: (byte & 0b0000_0100) != 0,
            b: (byte & 0b0000_0001) != 0,
        }
    }
}

#[inline]
fn decode_modrm(modrm: u8) -> (u8, u8, u8) {
    ((modrm >> 6) & 0b11, (modrm >> 3) & 0b111, modrm & 0b111)
}

#[inline]
fn read_u8(bytes: &[u8], pc: &mut usize) -> Result<u8, DisasmError> {
    if *pc >= bytes.len() {
        return Err(DisasmError::UnexpectedEof { offset: *pc });
    }
    let v = bytes[*pc];
    *pc += 1;
    Ok(v)
}

#[inline]
fn read_u32(bytes: &[u8], pc: &mut usize) -> Result<u32, DisasmError> {
    if bytes.len().saturating_sub(*pc) < 4 {
        return Err(DisasmError::UnexpectedEof { offset: *pc });
    }
    let v =
        u32::from_le_bytes(bytes[*pc..*pc + 4].try_into().expect("slice len"));
    *pc += 4;
    Ok(v)
}

#[inline]
fn read_u64(bytes: &[u8], pc: &mut usize) -> Result<u64, DisasmError> {
    if bytes.len().saturating_sub(*pc) < 8 {
        return Err(DisasmError::UnexpectedEof { offset: *pc });
    }
    let v =
        u64::from_le_bytes(bytes[*pc..*pc + 8].try_into().expect("slice len"));
    *pc += 8;
    Ok(v)
}

fn relative_target(
    next_pc: usize,
    disp: i32,
    offset: usize,
) -> Result<usize, DisasmError> {
    let target = (next_pc as i64) + (disp as i64);
    if target < 0 {
        return Err(DisasmError::InvalidRelativeTarget { offset, target });
    }
    Ok(target as usize)
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

fn collect_auto_labels(
    bytes: &[u8],
) -> Result<BTreeMap<usize, String>, DisasmError> {
    let mut targets = BTreeSet::new();
    let mut pc = 0usize;

    while pc < bytes.len() {
        let inst_start = pc;
        if matches!(bytes[pc], 0x40..=0x4F) {
            pc += 1;
            if pc >= bytes.len() {
                return Err(DisasmError::UnexpectedEof { offset: pc });
            }
        }

        let opcode = read_u8(bytes, &mut pc)?;
        match opcode {
            0xC3 | 0x50..=0x57 | 0x58..=0x5F => {}
            0xB8..=0xBF => {
                let _ = read_u64(bytes, &mut pc)?;
            }
            0x89 | 0x01 | 0x29 | 0x39 => {
                let modrm = read_u8(bytes, &mut pc)?;
                let (mode, _, _) = decode_modrm(modrm);
                if mode != 0b11 {
                    return Err(DisasmError::UnsupportedAddressing {
                        offset: inst_start,
                    });
                }
            }
            0x81 => {
                let modrm = read_u8(bytes, &mut pc)?;
                let (mode, reg_opcode, _) = decode_modrm(modrm);
                if mode != 0b11 || reg_opcode != 0b111 {
                    return Err(DisasmError::UnsupportedAddressing {
                        offset: inst_start,
                    });
                }
                let _ = read_u32(bytes, &mut pc)?;
            }
            0xE8 | 0xE9 => {
                let disp = read_u32(bytes, &mut pc)? as i32;
                let target = relative_target(pc, disp, inst_start)?;
                targets.insert(target);
            }
            0x0F => {
                let ext = read_u8(bytes, &mut pc)?;
                match ext {
                    0x84 | 0x85 => {
                        let disp = read_u32(bytes, &mut pc)? as i32;
                        let target = relative_target(pc, disp, inst_start)?;
                        targets.insert(target);
                    }
                    _ => {
                        return Err(DisasmError::UnsupportedOpcode {
                            offset: inst_start,
                            opcode: ext,
                        });
                    }
                }
            }
            _ => {
                return Err(DisasmError::UnsupportedOpcode {
                    offset: inst_start,
                    opcode,
                });
            }
        }
    }

    let mut labels = BTreeMap::new();
    for (idx, target) in targets.into_iter().enumerate() {
        labels.insert(target, format!("L{idx}"));
    }
    Ok(labels)
}

fn reg_name(idx: usize) -> &'static str {
    match idx {
        0 => "rax",
        1 => "rcx",
        2 => "rdx",
        3 => "rbx",
        4 => "rsp",
        5 => "rbp",
        6 => "rsi",
        7 => "rdi",
        8 => "r8",
        9 => "r9",
        10 => "r10",
        11 => "r11",
        12 => "r12",
        13 => "r13",
        14 => "r14",
        15 => "r15",
        _ => "<bad-reg>",
    }
}
