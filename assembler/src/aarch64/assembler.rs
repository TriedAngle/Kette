use std::fmt;
use std::ptr::{self, NonNull};

use heap::{map_memory, protect_memory_read_exec, unmap_memory, OS_PAGE_SIZE};

use super::disassembler::{
    disassemble, disassemble_with_options, DisasmError, DisasmOptions,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AssemblerError {
    LabelAlreadyBound { label: usize },
    LabelUnbound { label: usize },
    RelativeOutOfRange { label: usize },
    UnalignedBranchTarget { label: usize },
    EmptyFunction,
    MapExecutableFailed,
    ProtectExecutableFailed,
}

impl fmt::Display for AssemblerError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::LabelAlreadyBound { label } => {
                write!(f, "label L{label} is already bound")
            }
            Self::LabelUnbound { label } => {
                write!(f, "label L{label} is unbound")
            }
            Self::RelativeOutOfRange { label } => {
                write!(f, "relative displacement to L{label} is out of range")
            }
            Self::UnalignedBranchTarget { label } => {
                write!(
                    f,
                    "relative displacement to L{label} is not 4-byte aligned"
                )
            }
            Self::EmptyFunction => write!(f, "cannot finalize empty function"),
            Self::MapExecutableFailed => {
                write!(f, "failed to map executable memory")
            }
            Self::ProtectExecutableFailed => {
                write!(f, "failed to set executable page permissions")
            }
        }
    }
}

impl std::error::Error for AssemblerError {}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Label(usize);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum FixupKind {
    B26,
    BCond19,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Fixup {
    label: Label,
    instr_offset: usize,
    kind: FixupKind,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Reg {
    X0,
    X1,
    X2,
    X3,
    X4,
    X5,
    X6,
    X7,
    X8,
    X9,
    X10,
    X11,
    X12,
    X13,
    X14,
    X15,
    X16,
    X17,
    X18,
    X19,
    X20,
    X21,
    X22,
    X23,
    X24,
    X25,
    X26,
    X27,
    X28,
    X29,
    X30,
}

impl Reg {
    #[inline]
    fn enc(self) -> u8 {
        match self {
            Self::X0 => 0,
            Self::X1 => 1,
            Self::X2 => 2,
            Self::X3 => 3,
            Self::X4 => 4,
            Self::X5 => 5,
            Self::X6 => 6,
            Self::X7 => 7,
            Self::X8 => 8,
            Self::X9 => 9,
            Self::X10 => 10,
            Self::X11 => 11,
            Self::X12 => 12,
            Self::X13 => 13,
            Self::X14 => 14,
            Self::X15 => 15,
            Self::X16 => 16,
            Self::X17 => 17,
            Self::X18 => 18,
            Self::X19 => 19,
            Self::X20 => 20,
            Self::X21 => 21,
            Self::X22 => 22,
            Self::X23 => 23,
            Self::X24 => 24,
            Self::X25 => 25,
            Self::X26 => 26,
            Self::X27 => 27,
            Self::X28 => 28,
            Self::X29 => 29,
            Self::X30 => 30,
        }
    }
}

pub struct Assembler {
    name: String,
    bytes: Vec<u8>,
    labels: Vec<Option<usize>>,
    fixups: Vec<Fixup>,
}

impl Assembler {
    pub fn new() -> Self {
        Self::with_name("<anonymous>")
    }

    pub fn with_name(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            bytes: Vec::new(),
            labels: Vec::new(),
            fixups: Vec::new(),
        }
    }

    pub fn create_label(&mut self) -> Label {
        let idx = self.labels.len();
        self.labels.push(None);
        Label(idx)
    }

    pub fn bind_label(&mut self, label: Label) -> Result<(), AssemblerError> {
        let Some(slot) = self.labels.get_mut(label.0) else {
            return Err(AssemblerError::LabelUnbound { label: label.0 });
        };
        if slot.is_some() {
            return Err(AssemblerError::LabelAlreadyBound { label: label.0 });
        }
        *slot = Some(self.bytes.len());
        Ok(())
    }

    pub fn mov_ri64(&mut self, dst: Reg, imm: i64) {
        let imm = imm as u64;
        self.emit_movz(dst, (imm & 0xFFFF) as u16, 0);
        self.emit_movk(dst, ((imm >> 16) & 0xFFFF) as u16, 1);
        self.emit_movk(dst, ((imm >> 32) & 0xFFFF) as u16, 2);
        self.emit_movk(dst, ((imm >> 48) & 0xFFFF) as u16, 3);
    }

    pub fn mov_rr(&mut self, dst: Reg, src: Reg) {
        let insn =
            0xAA00_03E0u32 | ((src.enc() as u32) << 16) | (dst.enc() as u32);
        self.emit_u32(insn);
    }

    pub fn add_rr(&mut self, dst: Reg, src: Reg) {
        let insn = 0x8B00_0000u32
            | ((src.enc() as u32) << 16)
            | ((dst.enc() as u32) << 5)
            | (dst.enc() as u32);
        self.emit_u32(insn);
    }

    pub fn sub_rr(&mut self, dst: Reg, src: Reg) {
        let insn = 0xCB00_0000u32
            | ((src.enc() as u32) << 16)
            | ((dst.enc() as u32) << 5)
            | (dst.enc() as u32);
        self.emit_u32(insn);
    }

    pub fn cmp_rr(&mut self, lhs: Reg, rhs: Reg) {
        let insn = 0xEB00_001Fu32
            | ((rhs.enc() as u32) << 16)
            | ((lhs.enc() as u32) << 5);
        self.emit_u32(insn);
    }

    pub fn cmp_ri32(&mut self, reg: Reg, imm: i32) {
        if (0..=4095).contains(&imm) {
            let insn = 0xF100_001Fu32
                | ((imm as u32) << 10)
                | ((reg.enc() as u32) << 5);
            self.emit_u32(insn);
            return;
        }

        self.mov_ri64(Reg::X15, imm as i64);
        self.cmp_rr(reg, Reg::X15);
    }

    pub fn push_r(&mut self, reg: Reg) {
        self.emit_sub_sp_imm(16);
        self.emit_str_imm_sp(reg, 8);
    }

    pub fn pop_r(&mut self, reg: Reg) {
        self.emit_ldr_imm_sp(reg, 8);
        self.emit_add_sp_imm(16);
    }

    pub fn call_label(&mut self, label: Label) {
        let instr_offset = self.bytes.len();
        self.emit_u32(0x9400_0000);
        self.fixups.push(Fixup {
            label,
            instr_offset,
            kind: FixupKind::B26,
        });
    }

    pub fn jmp_label(&mut self, label: Label) {
        let instr_offset = self.bytes.len();
        self.emit_u32(0x1400_0000);
        self.fixups.push(Fixup {
            label,
            instr_offset,
            kind: FixupKind::B26,
        });
    }

    pub fn je_label(&mut self, label: Label) {
        let instr_offset = self.bytes.len();
        self.emit_u32(0x5400_0000);
        self.fixups.push(Fixup {
            label,
            instr_offset,
            kind: FixupKind::BCond19,
        });
    }

    pub fn jne_label(&mut self, label: Label) {
        let instr_offset = self.bytes.len();
        self.emit_u32(0x5400_0001);
        self.fixups.push(Fixup {
            label,
            instr_offset,
            kind: FixupKind::BCond19,
        });
    }

    pub fn ret(&mut self) {
        self.emit_u32(0xD65F_03C0);
    }

    pub fn finalize(mut self) -> Result<AssembledFunction, AssemblerError> {
        if self.bytes.is_empty() {
            return Err(AssemblerError::EmptyFunction);
        }

        self.resolve_fixups()?;

        let executable = ExecutableMemory::new(&self.bytes)?;

        Ok(AssembledFunction {
            name: self.name,
            bytes: self.bytes,
            executable,
        })
    }

    #[inline]
    fn emit_u32(&mut self, v: u32) {
        self.bytes.extend_from_slice(&v.to_le_bytes());
    }

    fn emit_movz(&mut self, dst: Reg, imm16: u16, hw: u32) {
        let insn = 0xD280_0000u32
            | ((hw & 0b11) << 21)
            | ((imm16 as u32) << 5)
            | dst.enc() as u32;
        self.emit_u32(insn);
    }

    fn emit_movk(&mut self, dst: Reg, imm16: u16, hw: u32) {
        let insn = 0xF280_0000u32
            | ((hw & 0b11) << 21)
            | ((imm16 as u32) << 5)
            | dst.enc() as u32;
        self.emit_u32(insn);
    }

    fn emit_sub_sp_imm(&mut self, imm: u32) {
        let insn = 0xD100_03FFu32 | ((imm & 0xFFF) << 10);
        self.emit_u32(insn);
    }

    fn emit_add_sp_imm(&mut self, imm: u32) {
        let insn = 0x9100_03FFu32 | ((imm & 0xFFF) << 10);
        self.emit_u32(insn);
    }

    fn emit_str_imm_sp(&mut self, src: Reg, byte_offset: u32) {
        let imm12 = (byte_offset / 8) & 0xFFF;
        let insn =
            0xF900_0000u32 | (imm12 << 10) | (31 << 5) | (src.enc() as u32);
        self.emit_u32(insn);
    }

    fn emit_ldr_imm_sp(&mut self, dst: Reg, byte_offset: u32) {
        let imm12 = (byte_offset / 8) & 0xFFF;
        let insn =
            0xF940_0000u32 | (imm12 << 10) | (31 << 5) | (dst.enc() as u32);
        self.emit_u32(insn);
    }

    fn resolve_fixups(&mut self) -> Result<(), AssemblerError> {
        for fixup in &self.fixups {
            let Some(target) = self.labels.get(fixup.label.0).and_then(|x| *x)
            else {
                return Err(AssemblerError::LabelUnbound {
                    label: fixup.label.0,
                });
            };

            let pc = fixup.instr_offset as i64;
            let disp_bytes = (target as i64) - pc;
            if (disp_bytes & 0b11) != 0 {
                return Err(AssemblerError::UnalignedBranchTarget {
                    label: fixup.label.0,
                });
            }
            let disp_words = disp_bytes >> 2;

            let mut insn = u32::from_le_bytes(
                self.bytes[fixup.instr_offset..fixup.instr_offset + 4]
                    .try_into()
                    .expect("instr"),
            );

            match fixup.kind {
                FixupKind::B26 => {
                    if !(-(1 << 25)..=(1 << 25) - 1).contains(&disp_words) {
                        return Err(AssemblerError::RelativeOutOfRange {
                            label: fixup.label.0,
                        });
                    }
                    insn = (insn & !0x03FF_FFFF)
                        | ((disp_words as i32 as u32) & 0x03FF_FFFF);
                }
                FixupKind::BCond19 => {
                    if !(-(1 << 18)..=(1 << 18) - 1).contains(&disp_words) {
                        return Err(AssemblerError::RelativeOutOfRange {
                            label: fixup.label.0,
                        });
                    }
                    insn = (insn & !(0x7_FFFF << 5))
                        | (((disp_words as i32 as u32) & 0x7_FFFF) << 5);
                }
            }

            self.bytes[fixup.instr_offset..fixup.instr_offset + 4]
                .copy_from_slice(&insn.to_le_bytes());
        }

        Ok(())
    }
}

impl Default for Assembler {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Debug)]
pub struct AssembledFunction {
    name: String,
    bytes: Vec<u8>,
    executable: ExecutableMemory,
}

impl AssembledFunction {
    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn machine_code(&self) -> &[u8] {
        &self.bytes
    }

    pub fn disassemble(&self) -> Result<String, DisasmError> {
        disassemble(&self.bytes)
    }

    pub fn disassemble_with_options(
        &self,
        options: &DisasmOptions<'_>,
    ) -> Result<String, DisasmError> {
        disassemble_with_options(&self.bytes, options)
    }

    pub fn entry_ptr(&self) -> *const u8 {
        self.executable.ptr.as_ptr() as *const u8
    }
}

#[derive(Debug)]
struct ExecutableMemory {
    ptr: NonNull<u8>,
    map_len: usize,
}

impl ExecutableMemory {
    fn new(code: &[u8]) -> Result<Self, AssemblerError> {
        let map_len = round_up_to_page(code.len().max(1));
        let ptr =
            map_memory(map_len).ok_or(AssemblerError::MapExecutableFailed)?;

        unsafe {
            ptr::copy_nonoverlapping(code.as_ptr(), ptr.as_ptr(), code.len())
        };

        if !protect_memory_read_exec(ptr, map_len) {
            unmap_memory(ptr, map_len);
            return Err(AssemblerError::ProtectExecutableFailed);
        }

        Ok(Self { ptr, map_len })
    }
}

impl Drop for ExecutableMemory {
    fn drop(&mut self) {
        unmap_memory(self.ptr, self.map_len);
    }
}

fn round_up_to_page(size: usize) -> usize {
    let page = OS_PAGE_SIZE;
    let rem = size % page;
    if rem == 0 {
        size
    } else {
        size + (page - rem)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn compile_one_insn(emit: impl FnOnce(&mut Assembler)) -> Vec<u8> {
        let mut a = Assembler::with_name("single");
        emit(&mut a);
        a.ret();
        a.finalize().expect("finalize").machine_code().to_vec()
    }

    #[test]
    fn encodes_mov_ri64() {
        let bytes =
            compile_one_insn(|a| a.mov_ri64(Reg::X0, 0x1122_3344_5566_7788));
        assert_eq!(bytes.len(), 20);
        let first = u32::from_le_bytes(bytes[0..4].try_into().expect("first"));
        assert_eq!(first & 0xFFC0_0000, 0xD280_0000);
    }

    #[test]
    fn encodes_mov_rr() {
        let bytes = compile_one_insn(|a| a.mov_rr(Reg::X0, Reg::X1));
        let insn = u32::from_le_bytes(bytes[0..4].try_into().expect("insn"));
        assert_eq!(insn, 0xAA01_03E0);
    }

    #[test]
    fn encodes_add_rr() {
        let bytes = compile_one_insn(|a| a.add_rr(Reg::X0, Reg::X1));
        let insn = u32::from_le_bytes(bytes[0..4].try_into().expect("insn"));
        assert_eq!(insn, 0x8B01_0000);
    }

    #[test]
    fn encodes_sub_rr() {
        let bytes = compile_one_insn(|a| a.sub_rr(Reg::X0, Reg::X1));
        let insn = u32::from_le_bytes(bytes[0..4].try_into().expect("insn"));
        assert_eq!(insn, 0xCB01_0000);
    }

    #[test]
    fn encodes_cmp_ri32_fast_path() {
        let bytes = compile_one_insn(|a| a.cmp_ri32(Reg::X0, 42));
        let insn = u32::from_le_bytes(bytes[0..4].try_into().expect("insn"));
        assert_eq!(insn & 0xFF00_001F, 0xF100_001F);
    }

    #[test]
    fn resolves_jmp_label_fixup() {
        let mut a = Assembler::with_name("jmp");
        let target = a.create_label();
        a.jmp_label(target);
        a.mov_rr(Reg::X0, Reg::X0);
        a.bind_label(target).expect("bind");
        a.ret();

        let func = a.finalize().expect("finalize");
        let first = u32::from_le_bytes(
            func.machine_code()[0..4].try_into().expect("i0"),
        );
        assert_eq!(first >> 26, 0b000101);
        assert_eq!(first & 0x03FF_FFFF, 2);
    }

    #[test]
    fn resolves_conditional_jumps() {
        let mut a = Assembler::with_name("jcc");
        let yes = a.create_label();
        let done = a.create_label();
        a.cmp_ri32(Reg::X0, 0);
        a.je_label(yes);
        a.mov_ri64(Reg::X0, 1);
        a.jmp_label(done);
        a.bind_label(yes).expect("bind yes");
        a.mov_ri64(Reg::X0, 2);
        a.bind_label(done).expect("bind done");
        a.ret();

        let func = a.finalize().expect("finalize");
        let asm = func.disassemble().expect("disassemble");
        assert!(asm.contains("b.eq L"));
        assert!(asm.contains("b L"));
    }

    #[test]
    fn disassembly_symbol_resolver_rewrites_targets() {
        let mut a = Assembler::with_name("symbols");
        let target = a.create_label();
        a.jmp_label(target);
        a.mov_ri64(Reg::X0, 1);
        a.bind_label(target).expect("bind target");
        a.ret();

        let func = a.finalize().expect("finalize");
        let opts = DisasmOptions {
            symbol_resolver: Some(&|offset| {
                if offset == 20 {
                    Some("L_target".to_string())
                } else {
                    None
                }
            }),
        };
        let asm = func.disassemble_with_options(&opts).expect("disassemble");
        assert!(asm.contains("b L_target"));
    }

    #[test]
    fn disassembly_emits_auto_label_definitions() {
        let mut a = Assembler::with_name("labels");
        let loop_start = a.create_label();
        a.bind_label(loop_start).expect("bind loop start");
        a.cmp_ri32(Reg::X0, 0);
        a.jne_label(loop_start);
        a.ret();

        let asm = a
            .finalize()
            .expect("finalize")
            .disassemble()
            .expect("disassemble");
        assert!(asm.contains("L0:"));
        assert!(asm.contains("b.ne L0"));
    }

    #[cfg(target_arch = "aarch64")]
    #[test]
    fn execute_returns_immediate_constant() {
        let mut a = Assembler::with_name("const42");
        a.mov_ri64(Reg::X0, 42);
        a.ret();
        let func = a.finalize().expect("finalize");

        let f: extern "C" fn() -> u64 =
            unsafe { std::mem::transmute(func.entry_ptr()) };
        assert_eq!(f(), 42);
    }

    #[cfg(target_arch = "aarch64")]
    #[test]
    fn execute_add_two_arguments() {
        let mut a = Assembler::with_name("add2");
        a.mov_rr(Reg::X2, Reg::X0);
        a.add_rr(Reg::X2, Reg::X1);
        a.mov_rr(Reg::X0, Reg::X2);
        a.ret();
        let func = a.finalize().expect("finalize");

        let f: extern "C" fn(u64, u64) -> u64 =
            unsafe { std::mem::transmute(func.entry_ptr()) };
        assert_eq!(f(10, 32), 42);
        assert_eq!(f(1, 2), 3);
    }

    #[cfg(target_arch = "aarch64")]
    #[test]
    fn execute_branching_path() {
        let mut a = Assembler::with_name("branch");
        let is_zero = a.create_label();
        let done = a.create_label();

        a.cmp_ri32(Reg::X0, 0);
        a.je_label(is_zero);
        a.mov_ri64(Reg::X0, 7);
        a.jmp_label(done);
        a.bind_label(is_zero).expect("bind zero");
        a.mov_ri64(Reg::X0, 9);
        a.bind_label(done).expect("bind done");
        a.ret();

        let func = a.finalize().expect("finalize");
        let f: extern "C" fn(u64) -> u64 =
            unsafe { std::mem::transmute(func.entry_ptr()) };
        assert_eq!(f(0), 9);
        assert_eq!(f(123), 7);
    }

    #[cfg(target_arch = "aarch64")]
    #[test]
    fn execute_complex_counted_loop_sum() {
        let mut a = Assembler::with_name("loop_sum");
        let loop_head = a.create_label();
        let done = a.create_label();

        a.mov_ri64(Reg::X1, 0);
        a.bind_label(loop_head).expect("bind loop");
        a.cmp_ri32(Reg::X0, 0);
        a.je_label(done);
        a.add_rr(Reg::X1, Reg::X0);
        a.mov_ri64(Reg::X2, 1);
        a.sub_rr(Reg::X0, Reg::X2);
        a.jmp_label(loop_head);
        a.bind_label(done).expect("bind done");
        a.mov_rr(Reg::X0, Reg::X1);
        a.ret();

        let func = a.finalize().expect("finalize");
        let f: extern "C" fn(u64) -> u64 =
            unsafe { std::mem::transmute(func.entry_ptr()) };
        assert_eq!(f(5), 15);
        assert_eq!(f(10), 55);
    }

    #[cfg(target_arch = "aarch64")]
    #[test]
    fn call_label_invokes_internal_function() {
        let mut a = Assembler::with_name("call_local");
        let callee = a.create_label();
        let done = a.create_label();

        a.call_label(callee);
        a.jmp_label(done);
        a.bind_label(callee).expect("bind callee");
        a.mov_ri64(Reg::X0, 55);
        a.ret();
        a.bind_label(done).expect("bind done");
        a.ret();

        let func = a.finalize().expect("finalize");
        let f: extern "C" fn() -> u64 =
            unsafe { std::mem::transmute(func.entry_ptr()) };
        assert_eq!(f(), 55);
    }

    #[test]
    fn duplicate_label_binding_errors() {
        let mut a = Assembler::with_name("dup");
        let l = a.create_label();
        a.bind_label(l).expect("first bind");
        let err = a.bind_label(l).expect_err("second bind should fail");
        assert!(matches!(err, AssemblerError::LabelAlreadyBound { .. }));
    }

    #[test]
    fn unbound_label_errors_on_finalize() {
        let mut a = Assembler::with_name("unbound");
        let l = a.create_label();
        a.jmp_label(l);
        a.ret();
        let err = a.finalize().expect_err("finalize should fail");
        assert!(matches!(err, AssemblerError::LabelUnbound { .. }));
    }

    #[test]
    fn empty_function_errors() {
        let a = Assembler::with_name("empty");
        let err = a.finalize().expect_err("finalize should fail");
        assert!(matches!(err, AssemblerError::EmptyFunction));
    }
}
