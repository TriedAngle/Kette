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
    Rel32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Fixup {
    label: Label,
    disp_offset: usize,
    instr_end: usize,
    kind: FixupKind,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Reg {
    Rax,
    Rcx,
    Rdx,
    Rbx,
    Rsp,
    Rbp,
    Rsi,
    Rdi,
    R8,
    R9,
    R10,
    R11,
    R12,
    R13,
    R14,
    R15,
}

impl Reg {
    #[inline]
    fn enc(self) -> u8 {
        match self {
            Self::Rax => 0,
            Self::Rcx => 1,
            Self::Rdx => 2,
            Self::Rbx => 3,
            Self::Rsp => 4,
            Self::Rbp => 5,
            Self::Rsi => 6,
            Self::Rdi => 7,
            Self::R8 => 8,
            Self::R9 => 9,
            Self::R10 => 10,
            Self::R11 => 11,
            Self::R12 => 12,
            Self::R13 => 13,
            Self::R14 => 14,
            Self::R15 => 15,
        }
    }

    #[inline]
    fn low3(self) -> u8 {
        self.enc() & 0b111
    }

    #[inline]
    fn high(self) -> bool {
        (self.enc() & 0b1000) != 0
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
        self.emit_rex(true, false, false, dst.high());
        self.emit_u8(0xB8 + dst.low3());
        self.emit_u64(imm as u64);
    }

    pub fn mov_rr(&mut self, dst: Reg, src: Reg) {
        self.emit_rex(true, src.high(), false, dst.high());
        self.emit_u8(0x89);
        self.emit_modrm(0b11, src.low3(), dst.low3());
    }

    pub fn add_rr(&mut self, dst: Reg, src: Reg) {
        self.emit_rex(true, src.high(), false, dst.high());
        self.emit_u8(0x01);
        self.emit_modrm(0b11, src.low3(), dst.low3());
    }

    pub fn sub_rr(&mut self, dst: Reg, src: Reg) {
        self.emit_rex(true, src.high(), false, dst.high());
        self.emit_u8(0x29);
        self.emit_modrm(0b11, src.low3(), dst.low3());
    }

    pub fn cmp_rr(&mut self, lhs: Reg, rhs: Reg) {
        self.emit_rex(true, rhs.high(), false, lhs.high());
        self.emit_u8(0x39);
        self.emit_modrm(0b11, rhs.low3(), lhs.low3());
    }

    pub fn cmp_ri32(&mut self, reg: Reg, imm: i32) {
        self.emit_rex(true, false, false, reg.high());
        self.emit_u8(0x81);
        self.emit_modrm(0b11, 0b111, reg.low3());
        self.emit_u32(imm as u32);
    }

    pub fn push_r(&mut self, reg: Reg) {
        self.emit_rex(false, false, false, reg.high());
        self.emit_u8(0x50 + reg.low3());
    }

    pub fn pop_r(&mut self, reg: Reg) {
        self.emit_rex(false, false, false, reg.high());
        self.emit_u8(0x58 + reg.low3());
    }

    pub fn call_label(&mut self, label: Label) {
        self.emit_u8(0xE8);
        let disp_offset = self.bytes.len();
        self.emit_u32(0);
        let instr_end = self.bytes.len();
        self.fixups.push(Fixup {
            label,
            disp_offset,
            instr_end,
            kind: FixupKind::Rel32,
        });
    }

    pub fn jmp_label(&mut self, label: Label) {
        self.emit_u8(0xE9);
        let disp_offset = self.bytes.len();
        self.emit_u32(0);
        let instr_end = self.bytes.len();
        self.fixups.push(Fixup {
            label,
            disp_offset,
            instr_end,
            kind: FixupKind::Rel32,
        });
    }

    pub fn je_label(&mut self, label: Label) {
        self.emit_u8(0x0F);
        self.emit_u8(0x84);
        let disp_offset = self.bytes.len();
        self.emit_u32(0);
        let instr_end = self.bytes.len();
        self.fixups.push(Fixup {
            label,
            disp_offset,
            instr_end,
            kind: FixupKind::Rel32,
        });
    }

    pub fn jne_label(&mut self, label: Label) {
        self.emit_u8(0x0F);
        self.emit_u8(0x85);
        let disp_offset = self.bytes.len();
        self.emit_u32(0);
        let instr_end = self.bytes.len();
        self.fixups.push(Fixup {
            label,
            disp_offset,
            instr_end,
            kind: FixupKind::Rel32,
        });
    }

    pub fn ret(&mut self) {
        self.emit_u8(0xC3);
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
    fn emit_u8(&mut self, v: u8) {
        self.bytes.push(v);
    }

    #[inline]
    fn emit_u32(&mut self, v: u32) {
        self.bytes.extend_from_slice(&v.to_le_bytes());
    }

    #[inline]
    fn emit_u64(&mut self, v: u64) {
        self.bytes.extend_from_slice(&v.to_le_bytes());
    }

    #[inline]
    fn emit_modrm(&mut self, mode: u8, reg: u8, rm: u8) {
        debug_assert!(mode < 4);
        debug_assert!(reg < 8);
        debug_assert!(rm < 8);
        self.emit_u8((mode << 6) | ((reg & 7) << 3) | (rm & 7));
    }

    #[inline]
    fn emit_rex(&mut self, w: bool, r: bool, x: bool, b: bool) {
        let rex = 0x40
            | ((w as u8) << 3)
            | ((r as u8) << 2)
            | ((x as u8) << 1)
            | (b as u8);
        if rex != 0x40 {
            self.emit_u8(rex);
        }
    }

    fn resolve_fixups(&mut self) -> Result<(), AssemblerError> {
        for fixup in &self.fixups {
            let Some(target) = self.labels.get(fixup.label.0).and_then(|x| *x)
            else {
                return Err(AssemblerError::LabelUnbound {
                    label: fixup.label.0,
                });
            };

            match fixup.kind {
                FixupKind::Rel32 => {
                    let disp = (target as i64) - (fixup.instr_end as i64);
                    if disp < i32::MIN as i64 || disp > i32::MAX as i64 {
                        return Err(AssemblerError::RelativeOutOfRange {
                            label: fixup.label.0,
                        });
                    }
                    let bytes = (disp as i32).to_le_bytes();
                    self.bytes[fixup.disp_offset..fixup.disp_offset + 4]
                        .copy_from_slice(&bytes);
                }
            }
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
            compile_one_insn(|a| a.mov_ri64(Reg::Rax, 0x1122_3344_5566_7788));
        assert_eq!(bytes[0], 0x48);
        assert_eq!(bytes[1], 0xB8);
        assert_eq!(
            &bytes[2..10],
            &[0x88, 0x77, 0x66, 0x55, 0x44, 0x33, 0x22, 0x11]
        );
        assert_eq!(bytes[10], 0xC3);
    }

    #[test]
    fn encodes_mov_rr_with_rex() {
        let bytes = compile_one_insn(|a| a.mov_rr(Reg::R8, Reg::R15));
        assert_eq!(&bytes[0..3], &[0x4D, 0x89, 0xF8]);
    }

    #[test]
    fn encodes_add_rr() {
        let bytes = compile_one_insn(|a| a.add_rr(Reg::Rax, Reg::Rdi));
        assert_eq!(&bytes[0..3], &[0x48, 0x01, 0xF8]);
    }

    #[test]
    fn encodes_sub_rr() {
        let bytes = compile_one_insn(|a| a.sub_rr(Reg::Rax, Reg::Rsi));
        assert_eq!(&bytes[0..3], &[0x48, 0x29, 0xF0]);
    }

    #[test]
    fn encodes_cmp_ri32() {
        let bytes = compile_one_insn(|a| a.cmp_ri32(Reg::Rdi, -1));
        assert_eq!(&bytes[0..3], &[0x48, 0x81, 0xFF]);
        assert_eq!(&bytes[3..7], &[0xFF, 0xFF, 0xFF, 0xFF]);
    }

    #[test]
    fn resolves_jmp_label_fixup() {
        let mut a = Assembler::with_name("jmp");
        let target = a.create_label();
        a.jmp_label(target);
        a.mov_ri64(Reg::Rax, 42);
        a.bind_label(target).expect("bind");
        a.ret();

        let func = a.finalize().expect("finalize");
        let bytes = func.machine_code();
        assert_eq!(bytes[0], 0xE9);
        let disp = i32::from_le_bytes(bytes[1..5].try_into().expect("disp"));
        assert_eq!(disp, 10);
    }

    #[test]
    fn resolves_conditional_jumps() {
        let mut a = Assembler::with_name("jcc");
        let yes = a.create_label();
        let done = a.create_label();
        a.cmp_ri32(Reg::Rdi, 0);
        a.je_label(yes);
        a.mov_ri64(Reg::Rax, 1);
        a.jmp_label(done);
        a.bind_label(yes).expect("bind yes");
        a.mov_ri64(Reg::Rax, 2);
        a.bind_label(done).expect("bind done");
        a.ret();

        let func = a.finalize().expect("finalize");
        let asm = func.disassemble().expect("disassemble");
        assert!(asm.contains("je L"));
        assert!(asm.contains("jmp L"));
    }

    #[test]
    fn disassembly_symbol_resolver_rewrites_targets() {
        let mut a = Assembler::with_name("symbols");
        let target = a.create_label();
        a.jmp_label(target);
        a.mov_ri64(Reg::Rax, 1);
        a.bind_label(target).expect("bind target");
        a.ret();

        let func = a.finalize().expect("finalize");
        let opts = DisasmOptions {
            symbol_resolver: Some(&|offset| {
                if offset == 0x000f {
                    Some("L_target".to_string())
                } else {
                    None
                }
            }),
        };
        let asm = func.disassemble_with_options(&opts).expect("disassemble");
        assert!(asm.contains("jmp L_target"));
    }

    #[test]
    fn disassembly_emits_auto_label_definitions() {
        let mut a = Assembler::with_name("labels");
        let loop_start = a.create_label();
        a.bind_label(loop_start).expect("bind loop start");
        a.cmp_ri32(Reg::Rdi, 0);
        a.jne_label(loop_start);
        a.ret();

        let asm = a
            .finalize()
            .expect("finalize")
            .disassemble()
            .expect("disassemble");
        assert!(asm.contains("L0:"));
        assert!(asm.contains("jne L0"));
    }

    #[test]
    fn execute_returns_immediate_constant() {
        let mut a = Assembler::with_name("const42");
        a.mov_ri64(Reg::Rax, 42);
        a.ret();
        let func = a.finalize().expect("finalize");

        let f: extern "C" fn() -> u64 =
            unsafe { std::mem::transmute(func.entry_ptr()) };
        assert_eq!(f(), 42);
    }

    #[test]
    fn execute_add_two_arguments() {
        let mut a = Assembler::with_name("add2");
        a.mov_rr(Reg::Rax, Reg::Rdi);
        a.add_rr(Reg::Rax, Reg::Rsi);
        a.ret();
        let func = a.finalize().expect("finalize");

        let f: extern "C" fn(u64, u64) -> u64 =
            unsafe { std::mem::transmute(func.entry_ptr()) };
        assert_eq!(f(10, 32), 42);
        assert_eq!(f(1, 2), 3);
    }

    #[test]
    fn execute_branching_path() {
        let mut a = Assembler::with_name("branch");
        let is_zero = a.create_label();
        let done = a.create_label();

        a.cmp_ri32(Reg::Rdi, 0);
        a.je_label(is_zero);
        a.mov_ri64(Reg::Rax, 7);
        a.jmp_label(done);
        a.bind_label(is_zero).expect("bind zero");
        a.mov_ri64(Reg::Rax, 9);
        a.bind_label(done).expect("bind done");
        a.ret();

        let func = a.finalize().expect("finalize");
        let f: extern "C" fn(u64) -> u64 =
            unsafe { std::mem::transmute(func.entry_ptr()) };
        assert_eq!(f(0), 9);
        assert_eq!(f(123), 7);
    }

    #[test]
    fn execute_complex_counted_loop_sum() {
        let mut a = Assembler::with_name("loop_sum");
        let loop_head = a.create_label();
        let done = a.create_label();

        a.mov_ri64(Reg::Rax, 0);
        a.bind_label(loop_head).expect("bind loop");
        a.cmp_ri32(Reg::Rdi, 0);
        a.je_label(done);
        a.add_rr(Reg::Rax, Reg::Rdi);
        a.mov_ri64(Reg::R10, 1);
        a.sub_rr(Reg::Rdi, Reg::R10);
        a.jmp_label(loop_head);
        a.bind_label(done).expect("bind done");
        a.ret();

        let func = a.finalize().expect("finalize");
        let f: extern "C" fn(u64) -> u64 =
            unsafe { std::mem::transmute(func.entry_ptr()) };
        assert_eq!(f(5), 15);
        assert_eq!(f(10), 55);
    }

    #[test]
    fn call_label_invokes_internal_function() {
        let mut a = Assembler::with_name("call_local");
        let callee = a.create_label();
        let done = a.create_label();

        a.call_label(callee);
        a.jmp_label(done);
        a.bind_label(callee).expect("bind callee");
        a.mov_ri64(Reg::Rax, 55);
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
