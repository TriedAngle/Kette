use std::collections::{HashMap, HashSet};

use bytecode::{BytecodeBuilder, SourceMapBuilder};
use object::{BigNum, Value};
use parser::ast::{
    AssignKind, Expr, ExprKind, KeywordPair, SlotDescriptor, SlotSelector,
};
use parser::semantic::{
    analyze_semantics_with_mode,
    collect_assignment_names as parser_collect_assignment_names,
    slot_selector_name, AnalysisMode,
};
use parser::span::{Pos, Span};

use crate::{CORE_MODULE, VM};

#[derive(Debug, Clone)]
struct ModuleCompileState {
    bindings: HashSet<String>,
    assignment_decls: HashSet<String>,
    imports: HashMap<String, (String, String)>,
    exports: HashSet<String>,
}

impl ModuleCompileState {
    fn empty() -> Self {
        Self {
            bindings: HashSet::new(),
            assignment_decls: HashSet::new(),
            imports: HashMap::new(),
            exports: HashSet::new(),
        }
    }
}

#[derive(Debug, Clone)]
struct CompileModuleEnv {
    initial_module: Option<String>,
    expr_modules: Vec<Option<String>>,
    modules: HashMap<String, ModuleCompileState>,
}

#[derive(Debug, Clone)]
pub struct CompileError {
    pub message: String,
    pub span: Option<Span>,
}

impl CompileError {
    fn new(msg: impl Into<String>, span: Span) -> Self {
        Self {
            message: msg.into(),
            span: Some(span),
        }
    }
    #[allow(dead_code)]
    fn no_span(msg: impl Into<String>) -> Self {
        Self {
            message: msg.into(),
            span: None,
        }
    }
}

impl std::fmt::Display for CompileError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(span) = &self.span {
            write!(
                f,
                "{}:{}: {}",
                span.start.line, span.start.column, self.message
            )
        } else {
            write!(f, "{}", self.message)
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ScopeKind {
    TopLevel,
    Object,
    Block,
}

#[derive(Debug, Clone, Copy)]
enum VarLoc {
    Local(u16),
    Temp(u16, u16),
    Global(u16),
}

#[derive(Debug, Clone)]
struct VarInfo {
    reg: u16,
    #[allow(dead_code)]
    mutable: bool,
    captured: bool,
    temp_idx: Option<u16>,
}

#[derive(Debug)]
struct Scope {
    #[allow(dead_code)]
    kind: ScopeKind,
    locals: Vec<(String, VarInfo)>,
    param_count: u16,
    next_reg: u16,
    max_reg: u16,
    temp_count: u16,
    feedback_count: u16,
}

impl Scope {
    fn new(kind: ScopeKind) -> Self {
        Self {
            kind,
            locals: Vec::new(),
            param_count: 0,
            next_reg: 1, // r0 = self
            max_reg: 1,
            temp_count: 0,
            feedback_count: 0,
        }
    }

    fn declare_local(&mut self, name: String, mutable: bool) -> u16 {
        if let Some((_, info)) = self.locals.iter().find(|(n, _)| *n == name) {
            return info.reg;
        }
        let reg = self.next_reg;
        self.next_reg += 1;
        if self.next_reg > self.max_reg {
            self.max_reg = self.next_reg;
        }
        self.locals.push((
            name,
            VarInfo {
                reg,
                mutable,
                captured: false,
                temp_idx: None,
            },
        ));
        reg
    }

    fn declare_param(&mut self, name: String) -> u16 {
        let reg = self.declare_local(name, false);
        self.param_count += 1;
        reg
    }

    fn alloc_temp(&mut self) -> u16 {
        let reg = self.next_reg;
        self.next_reg += 1;
        if self.next_reg > self.max_reg {
            self.max_reg = self.next_reg;
        }
        reg
    }

    fn find_local(&self, name: &str) -> Option<&VarInfo> {
        self.locals
            .iter()
            .rev()
            .find(|(n, _)| n == name)
            .map(|(_, v)| v)
    }

    #[allow(dead_code)]
    fn find_local_mut(&mut self, name: &str) -> Option<&mut VarInfo> {
        self.locals
            .iter_mut()
            .rev()
            .find(|(n, _)| n == name)
            .map(|(_, v)| v)
    }

    #[allow(dead_code)]
    fn has_local(&self, name: &str) -> bool {
        self.locals.iter().any(|(n, _)| n == name)
    }

    /// Mark a local variable as captured. Returns `true` if the variable
    /// was found (and marked), `false` otherwise.
    fn mark_captured(&mut self, name: &str) -> bool {
        for (n, var) in &mut self.locals {
            if n == name {
                var.captured = true;
                if var.temp_idx.is_none() {
                    let idx = self.temp_count;
                    self.temp_count += 1;
                    var.temp_idx = Some(idx);
                }
                return true;
            }
        }
        false
    }

    fn next_feedback(&mut self) -> u16 {
        let fb = self.feedback_count;
        self.feedback_count += 1;
        fb
    }

    fn reg_mark(&self) -> u16 {
        self.next_reg
    }

    fn restore_regs(&mut self, mark: u16) {
        self.next_reg = mark;
    }
}

// ── Output types ────────────────────────────────────────────────────

#[derive(Debug, Clone)]
pub struct CodeDesc {
    pub bytecode: Vec<u8>,
    pub constants: Vec<ConstEntry>,
    pub register_count: u16,
    pub arg_count: u16,
    pub temp_count: u16,
    pub feedback_count: u16,
    pub source_map: Vec<u8>,
}

#[derive(Debug, Clone)]
pub enum ConstEntry {
    Fixnum(i64),
    BigInt(i128),
    Float(f64),
    String(String),
    Value(Value),
    Symbol(String),
    ModuleAssoc { module: String, name: String },
    Assoc(String),
    AssocValue(String),
    Code(CodeDesc),
    Map(MapDesc),
}

#[derive(Debug, Clone)]
pub struct MapDesc {
    pub slots: Vec<SlotDesc>,
    pub value_count: u32,
    pub code: Option<usize>,
}

#[derive(Debug, Clone)]
pub struct SlotDesc {
    pub flags: u16,
    pub name: String,
    pub value: SlotValue,
}

#[derive(Debug, Clone)]
pub enum SlotValue {
    Constant(ConstEntry),
    Offset(u32),
}

// Slot flag constants matching object::SlotFlags
const SLOT_ASSIGNABLE: u16 = 1 << 0;
const SLOT_ASSIGNMENT: u16 = 1 << 1;
const SLOT_CONSTANT: u16 = 1 << 2;
const SLOT_ENUMERABLE: u16 = 1 << 3;
const SLOT_PARENT: u16 = 1 << 4;

// ── Compile frame ───────────────────────────────────────────────────

struct CompileFrame {
    scope: Scope,
    builder: BytecodeBuilder,
    constants: Vec<ConstEntry>,
    source_map: SourceMapBuilder,
}

// ── Compiler ────────────────────────────────────────────────────────

pub struct Compiler {
    frames: Vec<CompileFrame>,
    module_env: Option<CompileModuleEnv>,
    current_module: Option<String>,
    top_level_expr_index: usize,
}

impl Compiler {
    fn int_const_entry(value: i128) -> ConstEntry {
        if let Ok(v64) = i64::try_from(value) {
            let fixnum_min = -(BigNum::FIXNUM_MAX + 1);
            if (fixnum_min..=BigNum::FIXNUM_MAX).contains(&v64) {
                return ConstEntry::Fixnum(v64);
            }
        }
        ConstEntry::BigInt(value)
    }

    fn new() -> Self {
        Self {
            frames: Vec::new(),
            module_env: None,
            current_module: None,
            top_level_expr_index: 0,
        }
    }

    fn with_module_env(module_env: CompileModuleEnv) -> Self {
        Self {
            frames: Vec::new(),
            current_module: module_env.initial_module.clone(),
            module_env: Some(module_env),
            top_level_expr_index: 0,
        }
    }

    // ── Public API ──────────────────────────────────────────────

    pub fn compile(exprs: &[Expr]) -> Result<CodeDesc, CompileError> {
        match Self::compile_with_issues(exprs) {
            Ok(code) => Ok(code),
            Err(mut errs) => {
                if let Some(first) = errs.drain(..).next() {
                    Err(first)
                } else {
                    Err(CompileError::no_span("compile failed"))
                }
            }
        }
    }

    pub fn compile_with_issues(
        exprs: &[Expr],
    ) -> Result<CodeDesc, Vec<CompileError>> {
        let analysis =
            analyze_semantics_with_mode(&[], exprs, AnalysisMode::Strict);
        if !analysis.issues.is_empty() {
            let errs = analysis
                .issues
                .into_iter()
                .map(|issue| CompileError::new(issue.message, issue.span))
                .collect();
            return Err(errs);
        }

        let mut c = Compiler::new();
        c.compile_program(exprs).map_err(|err| vec![err])
    }

    pub fn compile_for_vm(
        vm: &VM,
        exprs: &[Expr],
    ) -> Result<CodeDesc, CompileError> {
        let module_env = build_compile_module_env(vm, exprs)?;
        let mut c = Compiler::with_module_env(module_env);
        c.compile_program(exprs)
    }

    fn compile_program(
        &mut self,
        exprs: &[Expr],
    ) -> Result<CodeDesc, CompileError> {
        self.push_frame(ScopeKind::TopLevel);
        self.prescan_locals(exprs);
        self.analyze_captures(exprs, &[]);

        let non_comment: Vec<&Expr> = exprs
            .iter()
            .filter(|e| !matches!(e.kind, ExprKind::Comment(_)))
            .collect();
        if non_comment.is_empty() {
            self.builder().load_local(0);
        } else {
            for (i, expr) in non_comment.iter().enumerate() {
                if let Some(env) = &self.module_env {
                    if let Some(module) =
                        env.expr_modules.get(self.top_level_expr_index).cloned()
                    {
                        self.current_module = module;
                    }
                }
                self.top_level_expr_index += 1;
                let mark = self.scope().reg_mark();
                self.compile_expr(expr)?;
                if i < non_comment.len() - 1 {
                    self.scope_mut().restore_regs(mark);
                }
            }
        }

        self.builder().local_return();
        Ok(self.pop_frame())
    }

    // ── Frame management ────────────────────────────────────────

    fn push_frame(&mut self, kind: ScopeKind) {
        self.frames.push(CompileFrame {
            scope: Scope::new(kind),
            builder: BytecodeBuilder::new(),
            constants: Vec::new(),
            source_map: SourceMapBuilder::new(),
        });
    }

    fn pop_frame(&mut self) -> CodeDesc {
        let frame = self.frames.pop().expect("no frame to pop");
        CodeDesc {
            bytecode: frame.builder.into_bytes(),
            register_count: frame.scope.max_reg,
            arg_count: frame.scope.param_count,
            temp_count: frame.scope.temp_count,
            feedback_count: frame.scope.feedback_count,
            constants: frame.constants,
            source_map: frame.source_map.finish(),
        }
    }

    fn frame(&self) -> &CompileFrame {
        self.frames.last().expect("no active frame")
    }

    fn frame_mut(&mut self) -> &mut CompileFrame {
        self.frames.last_mut().expect("no active frame")
    }

    fn scope(&self) -> &Scope {
        &self.frame().scope
    }

    fn scope_mut(&mut self) -> &mut Scope {
        &mut self.frame_mut().scope
    }

    fn builder(&mut self) -> &mut BytecodeBuilder {
        &mut self.frame_mut().builder
    }

    /// Record a source map entry mapping the current bytecode offset to a span.
    fn note(&mut self, span: Span) {
        let frame = self.frames.last_mut().expect("no active frame");
        let pc = frame.builder.current_offset() as u32;
        frame.source_map.add(
            pc,
            span.start.offset as u32,
            span.end.offset as u32,
        );
    }

    fn emit_captured_param_inits(&mut self, params: &[String]) {
        for param in params {
            let Some(var) = self.scope().find_local(param) else {
                continue;
            };
            let captured = var.captured;
            let idx = var.temp_idx;
            let reg = var.reg;
            if !captured {
                continue;
            }
            let Some(idx) = idx else {
                continue;
            };
            self.builder().mov_to_temp(0, idx, reg);
        }
    }

    // ── Constant pool ───────────────────────────────────────────

    fn add_constant(&mut self, entry: ConstEntry) -> u16 {
        let constants = &mut self.frame_mut().constants;
        let idx = constants.len() as u16;
        constants.push(entry);
        idx
    }

    fn add_symbol(&mut self, name: &str) -> u16 {
        let constants = &self.frame().constants;
        for (i, c) in constants.iter().enumerate() {
            if let ConstEntry::Symbol(s) = c {
                if s == name {
                    return i as u16;
                }
            }
        }
        self.add_constant(ConstEntry::Symbol(name.to_string()))
    }

    fn add_string_const(&mut self, s: &str) -> u16 {
        self.add_constant(ConstEntry::String(s.to_string()))
    }

    // ── Prescan: discover local variables ───────────────────────

    fn prescan_locals(&mut self, body: &[Expr]) {
        for expr in body {
            self.prescan_expr(expr);
        }
    }

    fn prescan_expr(&mut self, expr: &Expr) {
        match &expr.kind {
            ExprKind::Assignment { target, kind, .. } => {
                if let ExprKind::Ident(name) = &target.kind {
                    if self.scope().kind == ScopeKind::TopLevel {
                        return;
                    }
                    if *kind == AssignKind::Assign
                        && self.has_local_in_enclosing_scopes(name)
                    {
                        return;
                    }
                    let mutable = *kind == AssignKind::Assign;
                    self.scope_mut().declare_local(name.clone(), mutable);
                }
            }
            ExprKind::Sequence(exprs) => {
                for e in exprs {
                    self.prescan_expr(e);
                }
            }
            ExprKind::Paren(inner) => self.prescan_expr(inner),
            ExprKind::Cascade { messages, .. } => {
                for msg in messages {
                    self.prescan_expr(msg);
                }
            }
            // Don't recurse into Object or Block (different scopes)
            _ => {}
        }
    }

    // ── Capture analysis ────────────────────────────────────────

    fn analyze_captures(&mut self, body: &[Expr], shadows: &[HashSet<String>]) {
        for expr in body {
            self.analyze_capture_expr(expr, shadows);
        }
    }

    fn mark_captures_in_block(
        &mut self,
        body: &[Expr],
        shadow: &HashSet<String>,
    ) {
        for expr in body {
            self.mark_captures_in_block_expr(expr, shadow);
        }
    }

    fn mark_captures_in_block_expr(
        &mut self,
        expr: &Expr,
        shadow: &HashSet<String>,
    ) {
        match &expr.kind {
            ExprKind::Ident(name) => {
                if !shadow.contains(name.as_str()) {
                    self.mark_captured_if_found(name);
                }
            }
            ExprKind::Assignment { value, .. } => {
                self.mark_captures_in_block_expr(value, shadow);
            }
            ExprKind::Sequence(exprs) => {
                for e in exprs {
                    self.mark_captures_in_block_expr(e, shadow);
                }
            }
            ExprKind::Paren(inner) => {
                self.mark_captures_in_block_expr(inner, shadow);
            }
            ExprKind::UnaryMessage { receiver, .. } => {
                self.mark_captures_in_block_expr(receiver, shadow);
            }
            ExprKind::BinaryMessage {
                receiver, argument, ..
            } => {
                self.mark_captures_in_block_expr(receiver, shadow);
                self.mark_captures_in_block_expr(argument, shadow);
            }
            ExprKind::KeywordMessage { receiver, pairs } => {
                self.mark_captures_in_block_expr(receiver, shadow);
                for pair in pairs {
                    self.mark_captures_in_block_expr(&pair.argument, shadow);
                }
            }
            ExprKind::Cascade { receiver, messages } => {
                self.mark_captures_in_block_expr(receiver, shadow);
                for msg in messages {
                    self.mark_captures_in_block_expr(msg, shadow);
                }
            }
            ExprKind::Block { args, body } => {
                let mut nested = HashSet::new();
                for arg in args {
                    nested.insert(arg.clone());
                }
                self.collect_assignment_names_filtered(body, &mut nested);
                for expr in body {
                    self.mark_captures_in_block_expr(expr, &nested);
                }
            }
            ExprKind::Object { .. } => {
                // New scope; ignore here.
            }
            _ => {}
        }
    }

    fn analyze_capture_expr(
        &mut self,
        expr: &Expr,
        shadows: &[HashSet<String>],
    ) {
        match &expr.kind {
            ExprKind::Ident(name) => {
                if shadows.is_empty() {
                    // Directly in current scope — local ref, not a capture
                    return;
                }

                // If the innermost scope defines the name, it's local.
                if shadows.last().is_some_and(|s| s.contains(name.as_str())) {
                    return;
                }

                // Otherwise, try to mark capture (no-op if it's global).
                self.mark_captured_if_found(name);
            }
            ExprKind::Block { args, body } => {
                let mut shadow = HashSet::new();
                for arg in args {
                    shadow.insert(arg.clone());
                }
                self.collect_assignment_names_filtered(body, &mut shadow);
                let mut new_shadows = shadows.to_vec();
                new_shadows.push(shadow);
                self.mark_captures_in_block(body, new_shadows.last().unwrap());
                self.analyze_captures(body, &new_shadows);
            }
            ExprKind::Object { slots, body }
                if !body.is_empty()
                    || slots.iter().any(|s| !s.params.is_empty()) =>
            {
                // Method object — creates its own scope
                let mut shadow = HashSet::new();
                for slot in slots {
                    shadow.insert(slot_selector_name(slot));
                    for param in &slot.params {
                        shadow.insert(param.clone());
                    }
                }
                Self::collect_assignment_names(body, &mut shadow);
                let mut new_shadows = shadows.to_vec();
                new_shadows.push(shadow);
                self.analyze_captures(body, &new_shadows);
                for slot in slots {
                    if slot.shorthand {
                        let mut slot_shadows = new_shadows.clone();
                        if let Some(last) = slot_shadows.last_mut() {
                            last.remove(&slot_selector_name(slot));
                        }
                        self.analyze_capture_expr(&slot.value, &slot_shadows);
                    } else {
                        self.analyze_capture_expr(&slot.value, &new_shadows);
                    }
                }
            }
            ExprKind::Object { slots, .. } => {
                // Data object — no new scope
                for slot in slots {
                    self.analyze_capture_expr(&slot.value, shadows);
                }
            }
            ExprKind::UnaryMessage { receiver, .. } => {
                self.analyze_capture_expr(receiver, shadows);
            }
            ExprKind::BinaryMessage {
                receiver, argument, ..
            } => {
                self.analyze_capture_expr(receiver, shadows);
                self.analyze_capture_expr(argument, shadows);
            }
            ExprKind::KeywordMessage { receiver, pairs } => {
                self.analyze_capture_expr(receiver, shadows);
                for pair in pairs {
                    self.analyze_capture_expr(&pair.argument, shadows);
                }
            }
            ExprKind::Assignment {
                target,
                kind,
                value,
            } => {
                if *kind == AssignKind::Assign {
                    if let ExprKind::Ident(name) = &target.kind {
                        if shadows
                            .last()
                            .is_none_or(|s| !s.contains(name.as_str()))
                        {
                            self.mark_captured_if_found(name);
                        }
                    }
                }
                self.analyze_capture_expr(value, shadows);
            }
            ExprKind::Return(inner) | ExprKind::Paren(inner) => {
                self.analyze_capture_expr(inner, shadows);
            }
            ExprKind::Sequence(exprs) => {
                self.analyze_captures(exprs, shadows);
            }
            ExprKind::Cascade { receiver, messages } => {
                self.analyze_capture_expr(receiver, shadows);
                for msg in messages {
                    self.analyze_capture_expr(msg, shadows);
                }
            }
            ExprKind::Resend { message }
            | ExprKind::DirectedResend { message, .. } => {
                self.analyze_capture_expr(message, shadows);
            }
            // Leaves: Integer, Float, String, SelfRef, Comment, Error
            _ => {}
        }
    }

    fn mark_captured_if_found(&mut self, name: &str) {
        let depth = self.frames.len();
        if depth == 0 {
            return;
        }
        // Check current scope first
        if self.frames[depth - 1].scope.mark_captured(name) {
            return;
        }
        // Check enclosing scopes
        for i in (0..depth - 1).rev() {
            if self.frames[i].scope.mark_captured(name) {
                return;
            }
        }
        // Not found — global, nothing to mark
    }

    fn collect_assignment_names(body: &[Expr], out: &mut HashSet<String>) {
        out.extend(parser_collect_assignment_names(body));
    }

    fn collect_assignment_names_filtered(
        &self,
        body: &[Expr],
        out: &mut HashSet<String>,
    ) {
        for expr in body {
            match &expr.kind {
                ExprKind::Assignment { target, .. } => {
                    if let ExprKind::Ident(name) = &target.kind {
                        if !self.has_local_in_any_scope(name) {
                            out.insert(name.clone());
                        }
                    }
                }
                ExprKind::Sequence(exprs) => {
                    self.collect_assignment_names_filtered(exprs, out);
                }
                ExprKind::Paren(inner) => {
                    self.collect_assignment_names_filtered(
                        std::slice::from_ref(inner.as_ref()),
                        out,
                    );
                }
                _ => {}
            }
        }
    }

    // ── Variable resolution ─────────────────────────────────────

    fn resolve_for_store(
        &mut self,
        name: &str,
        kind: AssignKind,
        span: Span,
    ) -> Result<VarLoc, CompileError> {
        let depth = self.frames.len();

        // Check current scope
        if let Some(var) = self.frames[depth - 1].scope.find_local(name) {
            if kind == AssignKind::Assign && !var.mutable {
                return Err(CompileError::new(
                    "cannot assign to constant",
                    span,
                ));
            }
            if var.captured {
                return Ok(VarLoc::Temp(0, var.temp_idx.unwrap()));
            }
            return Ok(VarLoc::Local(var.reg));
        }

        // Check enclosing scopes
        for i in (0..depth - 1).rev() {
            if let Some(var) = self.frames[i].scope.find_local(name) {
                if kind == AssignKind::Assign && !var.mutable {
                    return Err(CompileError::new(
                        "cannot assign to constant",
                        span,
                    ));
                }
                if var.captured {
                    let array_idx = self.temp_array_depth(i);
                    return Ok(VarLoc::Temp(array_idx, var.temp_idx.unwrap()));
                }
                return Err(CompileError::new(
                    "assignment to non-captured outer variable",
                    span,
                ));
            }
        }

        if self.scope().kind == ScopeKind::TopLevel {
            let idx = self.add_global_ref(name, true, span)?;
            return Ok(VarLoc::Global(idx));
        }

        if kind == AssignKind::Assign {
            let reg = self.scope_mut().declare_local(name.to_string(), true);
            return Ok(VarLoc::Local(reg));
        }

        let reg = self.scope_mut().declare_local(name.to_string(), false);
        Ok(VarLoc::Local(reg))
    }

    fn has_local_in_enclosing_scopes(&self, name: &str) -> bool {
        if self.frames.len() <= 1 {
            return false;
        }
        for i in (0..self.frames.len() - 1).rev() {
            if self.frames[i].scope.find_local(name).is_some() {
                return true;
            }
        }
        false
    }

    fn has_local_in_any_scope(&self, name: &str) -> bool {
        for frame in self.frames.iter().rev() {
            if frame.scope.find_local(name).is_some() {
                return true;
            }
        }
        false
    }

    fn resolve_for_load(
        &mut self,
        name: &str,
        span: Span,
    ) -> Result<VarLoc, CompileError> {
        let depth = self.frames.len();

        // Check current scope
        if let Some(var) = self.frames[depth - 1].scope.find_local(name) {
            if var.captured {
                return Ok(VarLoc::Temp(0, var.temp_idx.unwrap()));
            }
            return Ok(VarLoc::Local(var.reg));
        }

        // Check enclosing scopes
        for i in (0..depth - 1).rev() {
            if let Some(var) = self.frames[i].scope.find_local(name) {
                if var.captured {
                    let array_idx = self.temp_array_depth(i);
                    return Ok(VarLoc::Temp(array_idx, var.temp_idx.unwrap()));
                }
                // Found in enclosing but not marked as captured — shouldn't
                // happen if capture analysis ran correctly. Treat as global.
                break;
            }
        }

        let idx = self.add_global_ref(name, false, span)?;
        Ok(VarLoc::Global(idx))
    }

    fn add_global_ref(
        &mut self,
        name: &str,
        is_store: bool,
        span: Span,
    ) -> Result<u16, CompileError> {
        if self.module_env.is_none() {
            return Ok(self.add_symbol(name));
        }

        let (module, export_name) =
            self.resolve_module_global(name, is_store, span)?;
        let constants = &self.frame().constants;
        for (i, c) in constants.iter().enumerate() {
            if let ConstEntry::ModuleAssoc { module: m, name: n } = c {
                if m == &module && n == &export_name {
                    return Ok(i as u16);
                }
            }
        }
        Ok(self.add_constant(ConstEntry::ModuleAssoc {
            module,
            name: export_name,
        }))
    }

    fn resolve_module_global(
        &self,
        name: &str,
        is_store: bool,
        span: Span,
    ) -> Result<(String, String), CompileError> {
        let Some(env) = &self.module_env else {
            return Err(CompileError::new(
                "module-aware compilation requires module environment",
                span,
            ));
        };

        if let Some((module_path, export_name)) = name.rsplit_once("::") {
            if is_store {
                return Err(CompileError::new(
                    format!(
                        "cannot assign to qualified export '{}': read-only",
                        name
                    ),
                    span,
                ));
            }

            let Some(module) = env.modules.get(module_path) else {
                return Err(CompileError::new(
                    format!("unknown module '{}'", module_path),
                    span,
                ));
            };

            if !module.exports.contains(export_name) {
                return Err(CompileError::new(
                    format!(
                        "unresolved global '{}' in module '{}'",
                        name, module_path
                    ),
                    span,
                ));
            }

            return Ok((module_path.to_string(), export_name.to_string()));
        }

        let Some(current_module) = &self.current_module else {
            return Err(CompileError::new(
                "no open module for global reference",
                span,
            ));
        };
        let Some(module) = env.modules.get(current_module) else {
            return Err(CompileError::new(
                format!("unknown current module '{current_module}'"),
                span,
            ));
        };

        if is_store {
            if let Some((target_module, target_name)) = module.imports.get(name)
            {
                return Ok((target_module.clone(), target_name.clone()));
            }
            if module.bindings.contains(name) {
                return Ok((current_module.clone(), name.to_string()));
            }

            return Ok((current_module.clone(), name.to_string()));
        }

        if module.bindings.contains(name) {
            return Ok((current_module.clone(), name.to_string()));
        }
        if let Some((target_module, target_name)) = module.imports.get(name) {
            return Ok((target_module.clone(), target_name.clone()));
        }

        Err(CompileError::new(
            format!(
                "unresolved global '{}' in module '{}'",
                name, current_module
            ),
            span,
        ))
    }

    fn resolve_lexical_for_load(
        &mut self,
        name: &str,
        skip_current_scope: bool,
    ) -> Option<VarLoc> {
        let depth = self.frames.len();
        if depth == 0 {
            return None;
        }

        if !skip_current_scope {
            if let Some(var) = self.frames[depth - 1].scope.find_local(name) {
                if var.captured {
                    return Some(VarLoc::Temp(0, var.temp_idx.unwrap()));
                }
                return Some(VarLoc::Local(var.reg));
            }
        }

        for i in (0..depth - 1).rev() {
            if let Some(var) = self.frames[i].scope.find_local(name) {
                if var.captured {
                    let array_idx = self.temp_array_depth(i);
                    return Some(VarLoc::Temp(
                        array_idx,
                        var.temp_idx.unwrap(),
                    ));
                }
                return None;
            }
        }

        None
    }

    fn temp_array_depth(&self, target_frame: usize) -> u16 {
        let current = self.frames.len().saturating_sub(1);
        let mut depth: u16 = 0;
        if target_frame >= current {
            return depth;
        }
        for i in (target_frame + 1)..=current {
            if self.frames[i].scope.temp_count > 0 {
                depth = depth.saturating_add(1);
            }
        }
        depth
    }

    // ── Body compilation ────────────────────────────────────────

    fn compile_body(&mut self, body: &[Expr]) -> Result<(), CompileError> {
        let non_comment: Vec<&Expr> = body
            .iter()
            .filter(|e| !matches!(e.kind, ExprKind::Comment(_)))
            .collect();

        if non_comment.is_empty() {
            // Empty body — load self as default return
            self.builder().load_local(0);
            return Ok(());
        }

        for (i, expr) in non_comment.iter().enumerate() {
            let mark = self.scope().reg_mark();
            self.compile_expr(expr)?;
            // Reset temp registers after each statement (except the last,
            // whose value stays in the accumulator)
            if i < non_comment.len() - 1 {
                self.scope_mut().restore_regs(mark);
            }
        }
        Ok(())
    }

    // ── Expression compilation ──────────────────────────────────

    fn compile_expr(&mut self, expr: &Expr) -> Result<(), CompileError> {
        self.note(expr.span);
        match &expr.kind {
            ExprKind::Integer(v) => {
                if let Ok(v32) = i32::try_from(*v) {
                    self.builder().load_smi(v32);
                } else {
                    let idx = self.add_constant(Self::int_const_entry(*v));
                    self.builder().load_constant(idx);
                }
            }
            ExprKind::Float(v) => {
                let idx = self.add_constant(ConstEntry::Float(*v));
                self.builder().load_constant(idx);
            }
            ExprKind::String(s) => {
                let idx = self.add_string_const(s);
                self.builder().load_constant(idx);
            }
            ExprKind::Symbol(s) => {
                let idx = self.add_symbol(s);
                self.builder().load_constant(idx);
            }
            ExprKind::SelfRef => {
                self.builder().load_local(0);
            }
            ExprKind::Ident(name) => {
                self.compile_ident(name, expr.span)?;
            }
            ExprKind::UnaryMessage { receiver, selector } => {
                self.compile_unary_message(receiver, selector, expr.span)?;
            }
            ExprKind::BinaryMessage {
                receiver,
                operator,
                argument,
            } => {
                self.compile_binary_message(
                    receiver, operator, argument, expr.span,
                )?;
            }
            ExprKind::KeywordMessage { receiver, pairs } => {
                self.compile_keyword_message(receiver, pairs, expr.span)?;
            }
            ExprKind::Assignment {
                target,
                kind,
                value,
            } => {
                self.compile_assignment(target, *kind, value)?;
            }
            ExprKind::Return(inner) => {
                self.compile_expr(inner)?;
                self.builder().return_();
            }
            ExprKind::Paren(inner) => {
                self.compile_expr(inner)?;
            }
            ExprKind::Sequence(exprs) => {
                self.compile_body(exprs)?;
            }
            ExprKind::Object { slots, body } => {
                self.compile_object(slots, body, &[])?;
            }
            ExprKind::Block { args, body } => {
                self.compile_block(args, body)?;
            }
            ExprKind::Cascade { receiver, messages } => {
                self.compile_cascade(receiver, messages)?;
            }
            ExprKind::Resend { message } => {
                self.compile_resend(message, None, expr.span)?;
            }
            ExprKind::DirectedResend { delegate, message } => {
                self.compile_resend(message, Some(delegate), expr.span)?;
            }
            ExprKind::Comment(_) => {
                // Skip
            }
            ExprKind::Error(msg) => {
                return Err(CompileError::new(msg.as_str(), expr.span));
            }
        }
        Ok(())
    }

    fn compile_ident(
        &mut self,
        name: &str,
        span: Span,
    ) -> Result<(), CompileError> {
        match self.resolve_for_load(name, span)? {
            VarLoc::Local(reg) => self.builder().load_local(reg),
            VarLoc::Temp(arr, idx) => self.builder().load_temp(arr, idx),
            VarLoc::Global(const_idx) => self.builder().load_assoc(const_idx),
        }
        Ok(())
    }

    fn compile_shorthand_value(
        &mut self,
        name: &str,
        skip_current_scope: bool,
        _span: Span,
    ) -> Result<(), CompileError> {
        if let Some(loc) =
            self.resolve_lexical_for_load(name, skip_current_scope)
        {
            match loc {
                VarLoc::Local(reg) => self.builder().load_local(reg),
                VarLoc::Temp(arr, idx) => self.builder().load_temp(arr, idx),
                VarLoc::Global(_) => {
                    // Not expected for lexical-only lookup.
                }
            }
        } else {
            let none_idx = self.add_symbol("None");
            self.builder().load_assoc(none_idx);
        }
        Ok(())
    }

    // ── Message compilation ─────────────────────────────────────

    fn compile_unary_message(
        &mut self,
        receiver: &Expr,
        selector: &str,
        msg_span: Span,
    ) -> Result<(), CompileError> {
        self.compile_expr(receiver)?;
        let sel_idx = self.add_symbol(selector);
        let fb = self.scope_mut().next_feedback();
        self.note(msg_span);
        self.builder().send(sel_idx, 0, 0, fb);
        Ok(())
    }

    fn compile_binary_message(
        &mut self,
        receiver: &Expr,
        operator: &str,
        argument: &Expr,
        msg_span: Span,
    ) -> Result<(), CompileError> {
        self.compile_expr(receiver)?;
        let tmp_recv = self.scope_mut().alloc_temp();
        self.builder().store_local(tmp_recv);

        self.compile_expr(argument)?;
        let tmp_arg = self.scope_mut().alloc_temp();
        self.builder().store_local(tmp_arg);

        self.builder().load_local(tmp_recv);
        let op_idx = self.add_symbol(operator);
        let fb = self.scope_mut().next_feedback();
        self.note(msg_span);
        self.builder().send(op_idx, tmp_arg, 1, fb);
        Ok(())
    }

    fn compile_keyword_message(
        &mut self,
        receiver: &Expr,
        pairs: &[KeywordPair],
        msg_span: Span,
    ) -> Result<(), CompileError> {
        self.compile_expr(receiver)?;
        let tmp_recv = self.scope_mut().alloc_temp();
        self.builder().store_local(tmp_recv);

        let mut arg_regs = Vec::with_capacity(pairs.len());
        for _ in pairs {
            arg_regs.push(self.scope_mut().alloc_temp());
        }
        for (pair, &arg_reg) in pairs.iter().zip(arg_regs.iter()) {
            self.compile_expr(&pair.argument)?;
            self.builder().store_local(arg_reg);
        }

        self.builder().load_local(tmp_recv);
        let selector: String =
            pairs.iter().map(|p| p.keyword.as_str()).collect();
        let sel_idx = self.add_symbol(&selector);
        let fb = self.scope_mut().next_feedback();
        let first_arg_reg = arg_regs.first().copied().unwrap_or(0);
        self.note(msg_span);
        self.builder()
            .send(sel_idx, first_arg_reg, pairs.len() as u8, fb);
        Ok(())
    }

    /// Compile just the message-send portion of a message expression,
    /// assuming the receiver is already in the accumulator.
    fn compile_message_tail(&mut self, msg: &Expr) -> Result<(), CompileError> {
        match &msg.kind {
            ExprKind::UnaryMessage { selector, .. } => {
                let sel_idx = self.add_symbol(selector);
                let fb = self.scope_mut().next_feedback();
                self.note(msg.span);
                self.builder().send(sel_idx, 0, 0, fb);
            }
            ExprKind::BinaryMessage {
                argument, operator, ..
            } => {
                let tmp_recv = self.scope_mut().alloc_temp();
                self.builder().store_local(tmp_recv);

                self.compile_expr(argument)?;
                let tmp_arg = self.scope_mut().alloc_temp();
                self.builder().store_local(tmp_arg);

                self.builder().load_local(tmp_recv);
                let op_idx = self.add_symbol(operator);
                let fb = self.scope_mut().next_feedback();
                self.note(msg.span);
                self.builder().send(op_idx, tmp_arg, 1, fb);
            }
            ExprKind::KeywordMessage { pairs, .. } => {
                let tmp_recv = self.scope_mut().alloc_temp();
                self.builder().store_local(tmp_recv);

                let mut arg_regs = Vec::with_capacity(pairs.len());
                for _ in pairs {
                    arg_regs.push(self.scope_mut().alloc_temp());
                }
                for (pair, &arg_reg) in pairs.iter().zip(arg_regs.iter()) {
                    self.compile_expr(&pair.argument)?;
                    self.builder().store_local(arg_reg);
                }

                self.builder().load_local(tmp_recv);
                let selector: String =
                    pairs.iter().map(|p| p.keyword.as_str()).collect();
                let sel_idx = self.add_symbol(&selector);
                let fb = self.scope_mut().next_feedback();
                let first_arg_reg = arg_regs.first().copied().unwrap_or(0);
                self.note(msg.span);
                self.builder().send(
                    sel_idx,
                    first_arg_reg,
                    pairs.len() as u8,
                    fb,
                );
            }
            _ => {
                // Shouldn't happen in a well-formed cascade
                self.compile_expr(msg)?;
            }
        }
        Ok(())
    }

    // ── Assignment ──────────────────────────────────────────────

    fn compile_assignment(
        &mut self,
        target: &Expr,
        kind: AssignKind,
        value: &Expr,
    ) -> Result<(), CompileError> {
        self.compile_expr(value)?;
        match &target.kind {
            ExprKind::Ident(name) => {
                let loc = self.resolve_for_store(name, kind, target.span)?;
                match loc {
                    VarLoc::Local(reg) => self.builder().store_local(reg),
                    VarLoc::Temp(arr, idx) => {
                        self.builder().store_temp(arr, idx)
                    }
                    VarLoc::Global(const_idx) => {
                        self.builder().store_assoc(const_idx)
                    }
                }
            }
            _ => {
                return Err(CompileError::new(
                    "assignment target must be an identifier",
                    target.span,
                ));
            }
        }
        Ok(())
    }

    // ── Cascade ─────────────────────────────────────────────────

    fn compile_cascade(
        &mut self,
        receiver: &Expr,
        messages: &[Expr],
    ) -> Result<(), CompileError> {
        self.compile_expr(receiver)?;
        let tmp_recv = self.scope_mut().alloc_temp();
        self.builder().store_local(tmp_recv);

        for msg in messages {
            self.builder().load_local(tmp_recv);
            self.compile_message_tail(msg)?;
        }
        Ok(())
    }

    // ── Resend ──────────────────────────────────────────────────

    fn compile_resend(
        &mut self,
        message: &Expr,
        delegate: Option<&String>,
        resend_span: Span,
    ) -> Result<(), CompileError> {
        match &message.kind {
            ExprKind::UnaryMessage { selector, .. } => {
                let sel_idx = self.add_symbol(selector);
                let fb = self.scope_mut().next_feedback();
                self.note(resend_span);
                if let Some(del) = delegate {
                    let del_idx = self.add_symbol(del);
                    self.builder().directed_resend(sel_idx, 0, 0, fb, del_idx);
                } else {
                    self.builder().resend(sel_idx, 0, 0, fb);
                }
            }
            ExprKind::BinaryMessage {
                argument, operator, ..
            } => {
                self.compile_expr(argument)?;
                let arg_reg = self.scope_mut().alloc_temp();
                self.builder().store_local(arg_reg);

                let sel_idx = self.add_symbol(operator);
                let fb = self.scope_mut().next_feedback();
                self.note(resend_span);
                if let Some(del) = delegate {
                    let del_idx = self.add_symbol(del);
                    self.builder()
                        .directed_resend(sel_idx, arg_reg, 1, fb, del_idx);
                } else {
                    self.builder().resend(sel_idx, arg_reg, 1, fb);
                }
            }
            ExprKind::KeywordMessage { pairs, .. } => {
                let first_arg_reg = self.scope().next_reg;
                for pair in pairs {
                    self.compile_expr(&pair.argument)?;
                    let tmp = self.scope_mut().alloc_temp();
                    self.builder().store_local(tmp);
                }

                let selector: String =
                    pairs.iter().map(|p| p.keyword.as_str()).collect();
                let sel_idx = self.add_symbol(&selector);
                let fb = self.scope_mut().next_feedback();
                let argc = pairs.len() as u8;
                self.note(resend_span);
                if let Some(del) = delegate {
                    let del_idx = self.add_symbol(del);
                    self.builder().directed_resend(
                        sel_idx,
                        first_arg_reg,
                        argc,
                        fb,
                        del_idx,
                    );
                } else {
                    self.builder().resend(sel_idx, first_arg_reg, argc, fb);
                }
            }
            _ => {
                return Err(CompileError::new(
                    "resend requires a message expression",
                    message.span,
                ));
            }
        }
        Ok(())
    }

    // ── Object compilation ──────────────────────────────────────

    fn compile_object(
        &mut self,
        slots: &[SlotDescriptor],
        body: &[Expr],
        parent_params: &[String],
    ) -> Result<(), CompileError> {
        let is_method = !body.is_empty() || !parent_params.is_empty();

        if is_method {
            self.compile_method_object(slots, body, parent_params)
        } else {
            self.compile_data_object(slots)
        }
    }

    fn compile_data_object(
        &mut self,
        slots: &[SlotDescriptor],
    ) -> Result<(), CompileError> {
        // Count assignable (mutable) slots for value_count
        let mut value_count: u32 = 0;
        let mut slot_descs = Vec::new();
        let mut value_regs = Vec::new();

        // Byte offset for assignable values
        // Values start at offset 16 (after Header + map pointer)
        let values_base_offset: u32 = 16;

        for slot in slots {
            let name = slot_selector_name(slot);
            let is_parent = slot.is_parent;
            let base_flags =
                SLOT_ENUMERABLE | if is_parent { SLOT_PARENT } else { 0 };

            if slot.mutable {
                // Mutable slot: ASSIGNABLE reader + ASSIGNMENT writer
                let offset = values_base_offset + value_count * 8;

                // Compile the value expression → temp register
                if slot.shorthand {
                    self.compile_shorthand_value(&name, false, slot.span)?;
                } else {
                    self.compile_expr(&slot.value)?;
                }
                let tmp = self.scope_mut().alloc_temp();
                self.builder().store_local(tmp);
                value_regs.push(tmp);

                // Reader slot
                slot_descs.push(SlotDesc {
                    flags: base_flags | SLOT_ASSIGNABLE,
                    name: name.clone(),
                    value: SlotValue::Offset(offset),
                });

                // Writer slot (name: appended)
                slot_descs.push(SlotDesc {
                    flags: base_flags | SLOT_ASSIGNMENT,
                    name: format!("{}:", name),
                    value: SlotValue::Offset(offset),
                });

                value_count += 1;
            } else {
                // Immutable slot: check if value is a nested method object
                let has_params = !slot.params.is_empty();
                let is_method_value = has_params
                    || matches!(&slot.value.kind, ExprKind::Object { body, .. } if !body.is_empty());

                if is_method_value {
                    // This slot's value is a method — compile as nested CodeDesc
                    let code_desc = self.compile_nested_method(slot)?;
                    slot_descs.push(SlotDesc {
                        flags: base_flags | SLOT_CONSTANT,
                        name,
                        value: SlotValue::Constant(ConstEntry::Code(code_desc)),
                    });
                } else {
                    if self.slot_value_requires_runtime(&slot.value) {
                        let offset = values_base_offset + value_count * 8;
                        if slot.shorthand {
                            self.compile_shorthand_value(
                                &name, false, slot.span,
                            )?;
                        } else {
                            self.compile_expr(&slot.value)?;
                        }
                        let tmp = self.scope_mut().alloc_temp();
                        self.builder().store_local(tmp);
                        value_regs.push(tmp);

                        // Read-only runtime value slot: assignable reader without writer.
                        slot_descs.push(SlotDesc {
                            flags: base_flags | SLOT_ASSIGNABLE,
                            name,
                            value: SlotValue::Offset(offset),
                        });
                        value_count += 1;
                    } else {
                        // Constant slot: value goes directly in the map.
                        let const_entry =
                            self.expr_to_const_entry(&slot.value)?;
                        slot_descs.push(SlotDesc {
                            flags: base_flags | SLOT_CONSTANT,
                            name,
                            value: SlotValue::Constant(const_entry),
                        });
                    }
                }
            }
        }

        let map_desc = MapDesc {
            slots: slot_descs,
            value_count,
            code: None,
        };
        let map_idx = self.add_constant(ConstEntry::Map(map_desc));

        let first_value_reg = if value_regs.is_empty() {
            0
        } else {
            let mut contiguous = true;
            for w in value_regs.windows(2) {
                if w[1] != w[0] + 1 {
                    contiguous = false;
                    break;
                }
            }

            if contiguous {
                value_regs[0]
            } else {
                let mut dst_regs = Vec::with_capacity(value_regs.len());
                for _ in 0..value_regs.len() {
                    dst_regs.push(self.scope_mut().alloc_temp());
                }

                for (&src, &dst) in value_regs.iter().zip(dst_regs.iter()) {
                    if src == dst {
                        continue;
                    }
                    self.builder().load_local(src);
                    self.builder().store_local(dst);
                }

                dst_regs[0]
            }
        };
        self.builder().create_object(map_idx, first_value_reg);

        Ok(())
    }

    fn compile_method_object(
        &mut self,
        slots: &[SlotDescriptor],
        body: &[Expr],
        parent_params: &[String],
    ) -> Result<(), CompileError> {
        // Enter a new scope for the method
        self.push_frame(ScopeKind::Object);

        // Register params
        for param in parent_params {
            self.scope_mut().declare_param(param.clone());
        }

        // Register slot names as locals
        for slot in slots {
            let name = slot_selector_name(slot);
            let mutable = slot.mutable;
            self.scope_mut().declare_local(name, mutable);
        }

        // Prescan body for additional locals
        self.prescan_locals(body);

        // Analyze captures (walks into nested scopes)
        self.analyze_captures(body, &[]);

        // Also analyze captures in slot values before initializing captured params.
        let mut shadow = HashSet::new();
        for slot in slots {
            shadow.insert(slot_selector_name(slot));
            for param in &slot.params {
                shadow.insert(param.clone());
            }
        }

        self.emit_captured_param_inits(parent_params);
        for param in parent_params {
            shadow.insert(param.clone());
        }
        let mut new_shadows = Vec::new();
        new_shadows.push(shadow);
        for slot in slots {
            if slot.shorthand {
                let mut slot_shadows = new_shadows.clone();
                if let Some(last) = slot_shadows.last_mut() {
                    last.remove(&slot_selector_name(slot));
                }
                self.analyze_capture_expr(&slot.value, &slot_shadows);
            } else {
                self.analyze_capture_expr(&slot.value, &new_shadows);
            }
        }

        // Compile slot initializers
        for slot in slots {
            let name = slot_selector_name(slot);
            if slot.shorthand {
                self.compile_shorthand_value(&name, true, slot.span)?;
            } else {
                self.compile_expr(&slot.value)?;
            }
            let (captured, reg, temp_idx) = {
                let var = self.scope().find_local(&name).expect("slot local");
                (var.captured, var.reg, var.temp_idx)
            };
            if captured {
                self.builder().store_temp(0, temp_idx.unwrap());
            } else {
                self.builder().store_local(reg);
            }
        }

        // Compile body
        self.compile_body(body)?;
        self.builder().local_return();

        let code_desc = self.pop_frame();

        // Build MapDesc for the method object
        let code_idx = self.add_constant(ConstEntry::Code(code_desc));
        let mut slot_descs = Vec::new();

        for slot in slots {
            let name = slot_selector_name(slot);
            let is_parent = slot.is_parent;
            let base_flags =
                SLOT_ENUMERABLE | if is_parent { SLOT_PARENT } else { 0 };

            // All slots in a method object are constant (stored in map)
            slot_descs.push(SlotDesc {
                flags: base_flags | SLOT_CONSTANT,
                name,
                value: SlotValue::Constant(ConstEntry::Symbol(
                    "slot".to_string(),
                )),
            });
        }

        let map_desc = MapDesc {
            slots: slot_descs,
            value_count: 0,
            code: Some(code_idx as usize),
        };
        let map_idx = self.add_constant(ConstEntry::Map(map_desc));
        self.builder().create_object(map_idx, 0);

        Ok(())
    }

    fn compile_nested_method(
        &mut self,
        slot: &SlotDescriptor,
    ) -> Result<CodeDesc, CompileError> {
        match &slot.value.kind {
            ExprKind::Object {
                slots: inner_slots,
                body,
            } => {
                self.push_frame(ScopeKind::Object);

                for param in &slot.params {
                    self.scope_mut().declare_param(param.clone());
                }

                for inner_slot in inner_slots {
                    let name = slot_selector_name(inner_slot);
                    self.scope_mut().declare_local(name, inner_slot.mutable);
                }

                self.prescan_locals(body);
                self.analyze_captures(body, &[]);

                // Analyze captures in slot values before initializing
                // captured params.
                let mut shadow = HashSet::new();
                for inner_slot in inner_slots {
                    shadow.insert(slot_selector_name(inner_slot));
                    for param in &inner_slot.params {
                        shadow.insert(param.clone());
                    }
                }
                for param in &slot.params {
                    shadow.insert(param.clone());
                }
                let mut new_shadows = Vec::new();
                new_shadows.push(shadow);
                for inner_slot in inner_slots {
                    if inner_slot.shorthand {
                        let mut slot_shadows = new_shadows.clone();
                        if let Some(last) = slot_shadows.last_mut() {
                            last.remove(&slot_selector_name(inner_slot));
                        }
                        self.analyze_capture_expr(
                            &inner_slot.value,
                            &slot_shadows,
                        );
                    } else {
                        self.analyze_capture_expr(
                            &inner_slot.value,
                            &new_shadows,
                        );
                    }
                }

                self.emit_captured_param_inits(&slot.params);

                for inner_slot in inner_slots {
                    let name = slot_selector_name(inner_slot);
                    if inner_slot.shorthand {
                        self.compile_shorthand_value(
                            &name,
                            true,
                            inner_slot.span,
                        )?;
                    } else {
                        self.compile_expr(&inner_slot.value)?;
                    }
                    let (captured, reg, temp_idx) = {
                        let var =
                            self.scope().find_local(&name).expect("slot local");
                        (var.captured, var.reg, var.temp_idx)
                    };
                    if captured {
                        self.builder().store_temp(0, temp_idx.unwrap());
                    } else {
                        self.builder().store_local(reg);
                    }
                }

                self.compile_body(body)?;
                self.builder().local_return();

                Ok(self.pop_frame())
            }
            _ => {
                // Slot value is not an Object — compile as a simple method
                // that returns the expression result
                self.push_frame(ScopeKind::Object);

                for param in &slot.params {
                    self.scope_mut().declare_param(param.clone());
                }

                self.compile_expr(&slot.value)?;
                self.builder().local_return();

                Ok(self.pop_frame())
            }
        }
    }

    /// Try to produce a ConstEntry from a simple expression (literals only).
    fn expr_to_const_entry(
        &mut self,
        expr: &Expr,
    ) -> Result<ConstEntry, CompileError> {
        match &expr.kind {
            ExprKind::Integer(v) => Ok(Self::int_const_entry(*v)),
            ExprKind::Float(v) => Ok(ConstEntry::Float(*v)),
            ExprKind::String(s) => Ok(ConstEntry::String(s.clone())),
            ExprKind::Symbol(s) => Ok(ConstEntry::Symbol(s.clone())),
            ExprKind::Ident(name) => Ok(ConstEntry::AssocValue(name.clone())),
            ExprKind::Object { slots, body } if body.is_empty() => {
                // Nested data object as a constant — build a MapDesc
                let mut slot_descs = Vec::new();
                for slot in slots {
                    let name = slot_selector_name(slot);
                    let const_val = self.expr_to_const_entry(&slot.value)?;
                    slot_descs.push(SlotDesc {
                        flags: SLOT_CONSTANT | SLOT_ENUMERABLE,
                        name,
                        value: SlotValue::Constant(const_val),
                    });
                }
                Ok(ConstEntry::Map(MapDesc {
                    slots: slot_descs,
                    value_count: 0,
                    code: None,
                }))
            }
            ExprKind::Block { args, body } => {
                // A block as a constant slot value
                let code = self.compile_block_inner(args, body)?;
                Ok(ConstEntry::Code(code))
            }
            _ => {
                // Non-trivial expression: compile it as a mini method that
                // evaluates the expression and returns it
                self.push_frame(ScopeKind::Object);
                self.compile_expr(expr)?;
                self.builder().local_return();
                Ok(ConstEntry::Code(self.pop_frame()))
            }
        }
    }

    fn slot_value_requires_runtime(&mut self, expr: &Expr) -> bool {
        match &expr.kind {
            ExprKind::Integer(_) | ExprKind::Float(_) | ExprKind::String(_) => {
                false
            }
            ExprKind::Ident(_) => true,
            ExprKind::Object { slots, body } => {
                if !body.is_empty() {
                    return true;
                }
                slots.iter().any(|s| {
                    !s.params.is_empty()
                        || self.slot_value_requires_runtime(&s.value)
                })
            }
            ExprKind::Block { .. } => false,
            _ => true,
        }
    }

    // ── Block compilation ───────────────────────────────────────

    fn compile_block(
        &mut self,
        args: &[String],
        body: &[Expr],
    ) -> Result<(), CompileError> {
        let code_desc = self.compile_block_inner(args, body)?;

        let code_idx = self.add_constant(ConstEntry::Code(code_desc));
        let map_desc = MapDesc {
            slots: Vec::new(),
            value_count: 0,
            code: Some(code_idx as usize),
        };
        let map_idx = self.add_constant(ConstEntry::Map(map_desc));
        self.builder().create_block(map_idx);

        Ok(())
    }

    fn compile_block_inner(
        &mut self,
        args: &[String],
        body: &[Expr],
    ) -> Result<CodeDesc, CompileError> {
        self.push_frame(ScopeKind::Block);

        for arg in args {
            self.scope_mut().declare_param(arg.clone());
        }

        self.prescan_locals(body);
        self.analyze_captures(body, &[]);

        self.emit_captured_param_inits(args);

        self.compile_body(body)?;
        self.builder().local_return();

        Ok(self.pop_frame())
    }
}

#[derive(Debug, Clone)]
enum ModuleDirective {
    Open {
        path: String,
    },
    Use {
        path: String,
    },
    UseAs {
        path: String,
        aliases: HashMap<String, String>,
    },
    UseOnly {
        path: String,
        names: HashSet<String>,
    },
    Export {
        name: String,
    },
}

#[derive(Debug, Clone)]
struct PendingUse {
    current_module: String,
    target_module: String,
    aliases: HashMap<String, String>,
    only_names: Option<HashSet<String>>,
    span: Span,
}

fn build_compile_module_env(
    vm: &VM,
    exprs: &[Expr],
) -> Result<CompileModuleEnv, CompileError> {
    let mut modules: HashMap<String, ModuleCompileState> = HashMap::new();
    for (path, module) in &vm.modules {
        let mut state = ModuleCompileState::empty();
        state.bindings.extend(module.bindings.keys().cloned());
        state.exports.extend(module.exports.iter().cloned());
        for (local, import) in &module.imports {
            state.imports.insert(
                local.clone(),
                (import.module_path.clone(), import.export_name.clone()),
            );
        }
        modules.insert(path.clone(), state);
    }

    let mut expr_modules = Vec::new();
    let mut current_module = vm.current_module.clone();
    let mut pending_uses = Vec::new();

    for expr in exprs {
        if matches!(expr.kind, ExprKind::Comment(_)) {
            continue;
        }
        expr_modules.push(current_module.clone());

        if let Some(name) = top_level_assignment_name(expr) {
            let Some(module) = &current_module else {
                return Err(CompileError::new(
                    "top-level assignment requires an open module",
                    expr.span,
                ));
            };
            let state = modules
                .entry(module.clone())
                .or_insert_with(ModuleCompileState::empty);
            state.bindings.insert(name.to_string());
            state.assignment_decls.insert(name.to_string());
        }

        if let Some(directive) = parse_module_directive(expr) {
            match directive {
                ModuleDirective::Open { path } => {
                    modules
                        .entry(path.clone())
                        .or_insert_with(ModuleCompileState::empty);
                    if path != CORE_MODULE {
                        modules
                            .entry(CORE_MODULE.to_string())
                            .or_insert_with(ModuleCompileState::empty);
                        pending_uses.push(PendingUse {
                            current_module: path.clone(),
                            target_module: CORE_MODULE.to_string(),
                            aliases: HashMap::new(),
                            only_names: None,
                            span: expr.span,
                        });
                    }
                    current_module = Some(path);
                }
                ModuleDirective::Export { name } => {
                    let Some(module) = current_module.clone() else {
                        return Err(CompileError::new(
                            "Module export requires an open module",
                            expr.span,
                        ));
                    };
                    modules
                        .entry(module)
                        .or_insert_with(ModuleCompileState::empty)
                        .exports
                        .insert(name);
                }
                ModuleDirective::Use { path } => {
                    let Some(module) = current_module.clone() else {
                        return Err(CompileError::new(
                            "Module use requires an open module",
                            expr.span,
                        ));
                    };
                    pending_uses.push(PendingUse {
                        current_module: module,
                        target_module: path,
                        aliases: HashMap::new(),
                        only_names: None,
                        span: expr.span,
                    });
                }
                ModuleDirective::UseAs { path, aliases } => {
                    let Some(module) = current_module.clone() else {
                        return Err(CompileError::new(
                            "Module use requires an open module",
                            expr.span,
                        ));
                    };
                    pending_uses.push(PendingUse {
                        current_module: module,
                        target_module: path,
                        aliases,
                        only_names: None,
                        span: expr.span,
                    });
                }
                ModuleDirective::UseOnly { path, names } => {
                    let Some(module) = current_module.clone() else {
                        return Err(CompileError::new(
                            "Module use requires an open module",
                            expr.span,
                        ));
                    };
                    pending_uses.push(PendingUse {
                        current_module: module,
                        target_module: path,
                        aliases: HashMap::new(),
                        only_names: Some(names),
                        span: expr.span,
                    });
                }
            }
        }
    }

    for use_dir in pending_uses {
        apply_compile_use(&mut modules, &use_dir)?;
    }

    for module in modules.values_mut() {
        let import_names: Vec<String> =
            module.imports.keys().cloned().collect();
        for name in import_names {
            if module.assignment_decls.contains(&name) {
                module.bindings.remove(&name);
            }
        }
    }

    for (module_name, module) in &modules {
        for export in &module.exports {
            if module.bindings.contains(export)
                || module.imports.contains_key(export)
            {
                continue;
            }
            return Err(CompileError::new(
                format!(
                    "module '{}' exports '{}' but it is not defined or imported",
                    module_name, export
                ),
                Span::point(Pos::origin()),
            ));
        }
    }

    Ok(CompileModuleEnv {
        initial_module: vm.current_module.clone(),
        expr_modules,
        modules,
    })
}

fn apply_compile_use(
    modules: &mut HashMap<String, ModuleCompileState>,
    use_dir: &PendingUse,
) -> Result<(), CompileError> {
    apply_compile_use_inner(modules, use_dir)
}

fn apply_compile_use_inner(
    modules: &mut HashMap<String, ModuleCompileState>,
    use_dir: &PendingUse,
) -> Result<(), CompileError> {
    let target = modules.get(&use_dir.target_module).ok_or_else(|| {
        CompileError::new(
            format!("unknown module '{}'", use_dir.target_module),
            use_dir.span,
        )
    })?;

    let target_exports = target.exports.clone();

    let selected_exports: HashSet<String> = match &use_dir.only_names {
        Some(only) => {
            for name in only {
                if !target_exports.contains(name) {
                    return Err(CompileError::new(
                        format!(
                            "cannot import non-exported symbol '{}' from module '{}'",
                            name, use_dir.target_module
                        ),
                        use_dir.span,
                    ));
                }
            }
            only.clone()
        }
        None => target_exports.clone(),
    };

    for from in use_dir.aliases.keys() {
        if !target_exports.contains(from) {
            return Err(CompileError::new(
                format!(
                    "cannot alias non-exported symbol '{}' from module '{}'",
                    from, use_dir.target_module
                ),
                use_dir.span,
            ));
        }
    }

    let current = modules
        .entry(use_dir.current_module.clone())
        .or_insert_with(ModuleCompileState::empty);

    for exported in &selected_exports {
        let local_name = use_dir
            .aliases
            .get(exported)
            .cloned()
            .unwrap_or_else(|| exported.clone());

        if current.bindings.contains(&local_name)
            && !current.assignment_decls.contains(&local_name)
        {
            return Err(CompileError::new(
                format!(
                    "import collision in module '{}': '{}' already exists",
                    use_dir.current_module, local_name
                ),
                use_dir.span,
            ));
        }

        if let Some(existing) = current.imports.get(&local_name) {
            if existing != &(use_dir.target_module.clone(), exported.clone()) {
                return Err(CompileError::new(
                    format!(
                        "import collision in module '{}': '{}' already exists",
                        use_dir.current_module, local_name
                    ),
                    use_dir.span,
                ));
            }
            continue;
        }

        current.imports.insert(
            local_name,
            (use_dir.target_module.clone(), exported.clone()),
        );
    }

    Ok(())
}

fn top_level_assignment_name(expr: &Expr) -> Option<&str> {
    match &expr.kind {
        ExprKind::Assignment { target, .. } => {
            if let ExprKind::Ident(name) = &target.kind {
                Some(name)
            } else {
                None
            }
        }
        _ => None,
    }
}

fn parse_module_directive(expr: &Expr) -> Option<ModuleDirective> {
    let ExprKind::KeywordMessage { receiver, pairs } = &expr.kind else {
        return None;
    };
    let ExprKind::Ident(receiver_name) = &receiver.kind else {
        return None;
    };

    if receiver_name == "Module" {
        return parse_module_directive_pairs(pairs);
    }
    if receiver_name == "VM" {
        return parse_vm_module_directive_pairs(pairs);
    }

    None
}

fn parse_module_directive_pairs(
    pairs: &[KeywordPair],
) -> Option<ModuleDirective> {
    if pairs.len() == 1 && pairs[0].keyword == "open:" {
        if let Some(path) = parse_symbol_arg(&pairs[0].argument) {
            return Some(ModuleDirective::Open { path });
        }
    }
    if pairs.len() == 1 && pairs[0].keyword == "use:" {
        if let Some(path) = parse_symbol_arg(&pairs[0].argument) {
            return Some(ModuleDirective::Use { path });
        }
    }
    if pairs.len() == 2
        && pairs[0].keyword == "use:"
        && pairs[1].keyword == "As:"
    {
        if let Some(path) = parse_symbol_arg(&pairs[0].argument) {
            let aliases = parse_alias_object(&pairs[1].argument)?;
            return Some(ModuleDirective::UseAs { path, aliases });
        }
    }
    if pairs.len() == 2
        && pairs[0].keyword == "use:"
        && pairs[1].keyword == "Only:"
    {
        if let Some(path) = parse_symbol_arg(&pairs[0].argument) {
            let names = parse_symbol_set_expr(&pairs[1].argument)?;
            return Some(ModuleDirective::UseOnly { path, names });
        }
    }
    if pairs.len() == 1 && pairs[0].keyword == "export:" {
        if let Some(name) = parse_symbol_arg(&pairs[0].argument) {
            return Some(ModuleDirective::Export { name });
        }
    }
    None
}

fn parse_vm_module_directive_pairs(
    pairs: &[KeywordPair],
) -> Option<ModuleDirective> {
    if pairs.len() == 1 && pairs[0].keyword == "_ModuleOpen:" {
        if let Some(path) = parse_symbol_arg(&pairs[0].argument) {
            return Some(ModuleDirective::Open { path });
        }
    }
    if pairs.len() == 1 && pairs[0].keyword == "_ModuleUse:" {
        if let Some(path) = parse_symbol_arg(&pairs[0].argument) {
            return Some(ModuleDirective::Use { path });
        }
    }
    if pairs.len() == 2
        && pairs[0].keyword == "_ModuleUse:"
        && pairs[1].keyword == "As:"
    {
        if let Some(path) = parse_symbol_arg(&pairs[0].argument) {
            let aliases = parse_alias_object(&pairs[1].argument)?;
            return Some(ModuleDirective::UseAs { path, aliases });
        }
    }
    if pairs.len() == 2
        && pairs[0].keyword == "_ModuleUseOnly:"
        && pairs[1].keyword == "Names:"
    {
        if let Some(path) = parse_symbol_arg(&pairs[0].argument) {
            let names = parse_symbol_set_expr(&pairs[1].argument)?;
            return Some(ModuleDirective::UseOnly { path, names });
        }
    }
    if pairs.len() == 1 && pairs[0].keyword == "_ModuleExport:" {
        if let Some(name) = parse_symbol_arg(&pairs[0].argument) {
            return Some(ModuleDirective::Export { name });
        }
    }
    None
}

fn parse_alias_object(expr: &Expr) -> Option<HashMap<String, String>> {
    let ExprKind::Object { slots, body } = &expr.kind else {
        return None;
    };
    if !body.is_empty() {
        return None;
    }

    let mut aliases = HashMap::new();
    for slot in slots {
        let SlotSelector::Unary(from) = &slot.selector else {
            return None;
        };
        let ExprKind::Symbol(to) = &slot.value.kind else {
            return None;
        };
        aliases.insert(from.clone(), to.clone());
    }
    Some(aliases)
}

fn parse_symbol_arg(expr: &Expr) -> Option<String> {
    match &expr.kind {
        ExprKind::Symbol(name) => Some(name.clone()),
        ExprKind::Paren(inner) => parse_symbol_arg(inner),
        _ => None,
    }
}

fn parse_symbol_set_expr(expr: &Expr) -> Option<HashSet<String>> {
    let mut out = HashSet::new();
    collect_symbol_expr(expr, &mut out)?;
    Some(out)
}

fn collect_symbol_expr(expr: &Expr, out: &mut HashSet<String>) -> Option<()> {
    match &expr.kind {
        ExprKind::Symbol(name) => {
            out.insert(name.clone());
            Some(())
        }
        ExprKind::Paren(inner) => collect_symbol_expr(inner, out),
        ExprKind::BinaryMessage {
            receiver,
            operator,
            argument,
        } if operator == "&" => {
            collect_symbol_expr(receiver, out)?;
            collect_symbol_expr(argument, out)?;
            Some(())
        }
        _ => None,
    }
}

// ── Tests ───────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use bytecode::{BytecodeDecoder, Instruction};
    use parser::{Lexer, Parser};

    fn parse_source(src: &str) -> Vec<Expr> {
        let lexer = Lexer::from_str(src);
        Parser::new(lexer)
            .map(|r| r.expect("parse error"))
            .collect()
    }

    fn compile_source(src: &str) -> CodeDesc {
        let exprs = parse_source(src);
        Compiler::compile(&exprs).expect("compile error")
    }

    fn decode(code: &CodeDesc) -> Vec<Instruction> {
        BytecodeDecoder::new(&code.bytecode).collect()
    }

    // ── Milestone 1: Literals ───────────────────────────────────

    #[test]
    fn compile_small_integer() {
        let code = compile_source("42");
        let instrs = decode(&code);
        assert_eq!(
            instrs,
            vec![Instruction::LoadSmi { value: 42 }, Instruction::LocalReturn,]
        );
    }

    #[test]
    fn compile_negative_integer() {
        let code = compile_source("-7");
        let instrs = decode(&code);
        assert_eq!(
            instrs,
            vec![Instruction::LoadSmi { value: -7 }, Instruction::LocalReturn,]
        );
    }

    #[test]
    fn compile_large_integer_as_bignum_const() {
        let code = compile_source("18446744073709551615");
        let instrs = decode(&code);
        assert_eq!(
            instrs,
            vec![
                Instruction::LoadConstant { idx: 0 },
                Instruction::LocalReturn,
            ]
        );
        assert!(matches!(
            code.constants[0],
            ConstEntry::BigInt(18_446_744_073_709_551_615)
        ));
    }

    #[test]
    fn compile_float() {
        let code = compile_source("3.14");
        let instrs = decode(&code);
        assert_eq!(
            instrs,
            vec![
                Instruction::LoadConstant { idx: 0 },
                Instruction::LocalReturn,
            ]
        );
        assert!(
            matches!(code.constants[0], ConstEntry::Float(v) if (v - 3.14).abs() < 1e-10)
        );
    }

    #[test]
    fn compile_string() {
        let code = compile_source("\"hello\"");
        let instrs = decode(&code);
        assert_eq!(
            instrs,
            vec![
                Instruction::LoadConstant { idx: 0 },
                Instruction::LocalReturn,
            ]
        );
        assert!(
            matches!(&code.constants[0], ConstEntry::String(s) if s == "hello")
        );
    }

    #[test]
    fn compile_self() {
        let code = compile_source("self");
        let instrs = decode(&code);
        assert_eq!(
            instrs,
            vec![Instruction::LoadLocal { reg: 0 }, Instruction::LocalReturn,]
        );
    }

    #[test]
    fn compile_sequence() {
        let code = compile_source("1. 2. 3");
        let instrs = decode(&code);
        assert_eq!(
            instrs,
            vec![
                Instruction::LoadSmi { value: 1 },
                Instruction::LoadSmi { value: 2 },
                Instruction::LoadSmi { value: 3 },
                Instruction::LocalReturn,
            ]
        );
    }

    // ── Milestone 2: Locals + Messages ──────────────────────────

    #[test]
    fn compile_assignment_and_load() {
        let code = compile_source("[ x = 5. x ]");
        let block_code = find_code_const(&code.constants);
        let instrs = decode(block_code);
        assert_eq!(
            instrs,
            vec![
                Instruction::LoadSmi { value: 5 },
                Instruction::StoreLocal { reg: 1 }, // x = r1
                Instruction::LoadLocal { reg: 1 },
                Instruction::LocalReturn,
            ]
        );
    }

    #[test]
    fn compile_unary_message() {
        let code = compile_source("5 factorial");
        let instrs = decode(&code);
        assert_eq!(
            instrs,
            vec![
                Instruction::LoadSmi { value: 5 },
                Instruction::Send {
                    message_idx: 0,
                    reg: 0,
                    argc: 0,
                    feedback_idx: 0
                },
                Instruction::LocalReturn,
            ]
        );
        assert!(
            matches!(&code.constants[0], ConstEntry::Symbol(s) if s == "factorial")
        );
    }

    #[test]
    fn compile_binary_message() {
        let code = compile_source("3 + 4");
        let instrs = decode(&code);
        // r0=self, r1=tmp_recv, r2=tmp_arg
        assert_eq!(
            instrs,
            vec![
                Instruction::LoadSmi { value: 3 },
                Instruction::StoreLocal { reg: 1 }, // save receiver
                Instruction::LoadSmi { value: 4 },
                Instruction::StoreLocal { reg: 2 }, // save arg
                Instruction::LoadLocal { reg: 1 },  // receiver to acc
                Instruction::Send {
                    message_idx: 0,
                    reg: 2,
                    argc: 1,
                    feedback_idx: 0
                },
                Instruction::LocalReturn,
            ]
        );
        assert!(
            matches!(&code.constants[0], ConstEntry::Symbol(s) if s == "+")
        );
    }

    #[test]
    fn compile_keyword_message() {
        let code = compile_source("5 min: 3");
        let instrs = decode(&code);
        assert_eq!(
            instrs,
            vec![
                Instruction::LoadSmi { value: 5 },
                Instruction::StoreLocal { reg: 1 }, // save receiver
                Instruction::LoadSmi { value: 3 },
                Instruction::StoreLocal { reg: 2 }, // save arg
                Instruction::LoadLocal { reg: 1 },  // receiver to acc
                Instruction::Send {
                    message_idx: 0,
                    reg: 2,
                    argc: 1,
                    feedback_idx: 0
                },
                Instruction::LocalReturn,
            ]
        );
        assert!(
            matches!(&code.constants[0], ConstEntry::Symbol(s) if s == "min:")
        );
    }

    #[test]
    fn compile_multi_keyword_message() {
        let code = compile_source("self foo: 1 Bar: 2");
        let instrs = decode(&code);
        assert_eq!(
            instrs,
            vec![
                Instruction::LoadLocal { reg: 0 },  // self
                Instruction::StoreLocal { reg: 1 }, // save receiver
                Instruction::LoadSmi { value: 1 },
                Instruction::StoreLocal { reg: 2 }, // arg 1
                Instruction::LoadSmi { value: 2 },
                Instruction::StoreLocal { reg: 3 }, // arg 2
                Instruction::LoadLocal { reg: 1 },  // receiver to acc
                Instruction::Send {
                    message_idx: 0,
                    reg: 2,
                    argc: 2,
                    feedback_idx: 0
                },
                Instruction::LocalReturn,
            ]
        );
        assert!(
            matches!(&code.constants[0], ConstEntry::Symbol(s) if s == "foo:Bar:")
        );
    }

    #[test]
    fn compile_keyword_message_arg_registers_with_complex_arg() {
        let code = compile_source("Object _Extend: o With: { x := 7 }");
        let instrs = decode(&code);
        let send_pos = instrs
            .iter()
            .rposition(|i| matches!(i, Instruction::Send { argc: 2, .. }))
            .expect("missing send");
        let send_reg = match instrs[send_pos] {
            Instruction::Send { reg, .. } => reg,
            _ => unreachable!(),
        };
        assert_eq!(send_reg, 2);

        let mut last_store = None;
        for instr in instrs[..send_pos].iter().rev() {
            if let Instruction::StoreLocal { reg } = instr {
                last_store = Some(*reg);
                break;
            }
        }
        assert_eq!(last_store, Some(3));
    }

    #[test]
    fn compile_local_assignment_and_binary() {
        let code = compile_source("[ x = 5. x + 3 ]");
        let block_code = find_code_const(&code.constants);
        let instrs = decode(block_code);
        // r1 = x (from prescan)
        // After "x = 5": r1 holds 5
        // For "x + 3": r2 = tmp_recv, r3 = tmp_arg
        assert_eq!(
            instrs,
            vec![
                // x = 5
                Instruction::LoadSmi { value: 5 },
                Instruction::StoreLocal { reg: 1 },
                // x + 3
                Instruction::LoadLocal { reg: 1 },
                Instruction::StoreLocal { reg: 2 }, // save x (receiver)
                Instruction::LoadSmi { value: 3 },
                Instruction::StoreLocal { reg: 3 }, // save 3 (arg)
                Instruction::LoadLocal { reg: 2 },  // x back to acc
                Instruction::Send {
                    message_idx: 0,
                    reg: 3,
                    argc: 1,
                    feedback_idx: 0
                },
                Instruction::LocalReturn,
            ]
        );
    }

    #[test]
    fn compile_return() {
        let code = compile_source("^ 42");
        let instrs = decode(&code);
        assert_eq!(
            instrs,
            vec![
                Instruction::LoadSmi { value: 42 },
                Instruction::Return,
                Instruction::LocalReturn,
            ]
        );
    }

    #[test]
    fn compile_paren() {
        let code = compile_source("(3 + 4)");
        let instrs = decode(&code);
        assert_eq!(
            instrs,
            vec![
                Instruction::LoadSmi { value: 3 },
                Instruction::StoreLocal { reg: 1 },
                Instruction::LoadSmi { value: 4 },
                Instruction::StoreLocal { reg: 2 },
                Instruction::LoadLocal { reg: 1 },
                Instruction::Send {
                    message_idx: 0,
                    reg: 2,
                    argc: 1,
                    feedback_idx: 0
                },
                Instruction::LocalReturn,
            ]
        );
    }

    // ── Milestone 3: Objects ────────────────────────────────────

    #[test]
    fn compile_empty_data_object() {
        let code = compile_source("{}");
        let instrs = decode(&code);
        assert_eq!(
            instrs,
            vec![
                Instruction::CreateObject {
                    map_idx: 0,
                    values_reg: 0
                },
                Instruction::LocalReturn,
            ]
        );
        assert!(
            matches!(&code.constants[0], ConstEntry::Map(m) if m.slots.is_empty())
        );
    }

    #[test]
    fn compile_data_object_const_slot() {
        let code = compile_source("{ x = 5 }");
        let instrs = decode(&code);
        assert_eq!(
            instrs,
            vec![
                Instruction::CreateObject {
                    map_idx: 0,
                    values_reg: 0
                },
                Instruction::LocalReturn,
            ]
        );
        let map = match &code.constants[0] {
            ConstEntry::Map(m) => m,
            _ => panic!("expected map"),
        };
        assert_eq!(map.slots.len(), 1);
        assert_eq!(map.slots[0].name, "x");
        assert!(map.slots[0].flags & SLOT_CONSTANT != 0);
        assert!(matches!(
            &map.slots[0].value,
            SlotValue::Constant(ConstEntry::Fixnum(5))
        ));
    }

    #[test]
    fn compile_data_object_mutable_slot() {
        let code = compile_source("{ x := 5 }");
        let instrs = decode(&code);
        // Compile 5 → store in tmp register → CreateObject
        assert_eq!(
            instrs,
            vec![
                Instruction::LoadSmi { value: 5 },
                Instruction::StoreLocal { reg: 1 }, // tmp for value
                Instruction::CreateObject {
                    map_idx: 0,
                    values_reg: 1
                },
                Instruction::LocalReturn,
            ]
        );
        let map = match &code.constants[0] {
            ConstEntry::Map(m) => m,
            _ => panic!("expected map"),
        };
        assert_eq!(map.slots.len(), 2); // reader + writer
        assert_eq!(map.value_count, 1);
        assert_eq!(map.slots[0].name, "x");
        assert!(map.slots[0].flags & SLOT_ASSIGNABLE != 0);
        assert_eq!(map.slots[1].name, "x:");
        assert!(map.slots[1].flags & SLOT_ASSIGNMENT != 0);
    }

    // ── Milestone 4: Blocks ─────────────────────────────────────

    #[test]
    fn compile_empty_block() {
        let code = compile_source("[]");
        let instrs = decode(&code);
        // CreateBlock with map_idx pointing to a Map constant
        assert_eq!(instrs.len(), 2); // CreateBlock + LocalReturn
        assert!(matches!(instrs[0], Instruction::CreateBlock { .. }));
        assert_eq!(instrs[1], Instruction::LocalReturn);
    }

    #[test]
    fn compile_block_with_args() {
        let code = compile_source("[ | x | x + 1 ]");
        let instrs = decode(&code);
        assert!(matches!(instrs[0], Instruction::CreateBlock { .. }));

        // Check the block's CodeDesc
        let block_code = find_code_const(&code.constants);
        assert_eq!(block_code.arg_count, 1);
        let block_instrs = decode(block_code);
        // x is r1 (param), tmp_recv=r2, tmp_arg=r3
        assert_eq!(
            block_instrs,
            vec![
                Instruction::LoadLocal { reg: 1 },  // x
                Instruction::StoreLocal { reg: 2 }, // save receiver
                Instruction::LoadSmi { value: 1 },
                Instruction::StoreLocal { reg: 3 }, // save arg
                Instruction::LoadLocal { reg: 2 },  // receiver to acc
                Instruction::Send {
                    message_idx: 0,
                    reg: 3,
                    argc: 1,
                    feedback_idx: 0
                },
                Instruction::LocalReturn,
            ]
        );
    }

    #[test]
    fn compile_block_captures_local() {
        let code = compile_source("[ y = 10. [ y + 1 ] ]");
        let outer_block = find_code_const(&code.constants);
        let outer_instrs = decode(outer_block);

        // In outer block: y is captured → stored via StoreTemp
        assert_eq!(outer_instrs[0], Instruction::LoadSmi { value: 10 });
        assert_eq!(
            outer_instrs[1],
            Instruction::StoreTemp {
                array_idx: 0,
                idx: 0
            }
        );

        // Inner block creation
        assert!(matches!(outer_instrs[2], Instruction::CreateBlock { .. }));

        // Inside the inner block: y accessed via LoadTemp
        let inner_block = find_code_const(&outer_block.constants);
        let inner_instrs = decode(inner_block);
        assert_eq!(
            inner_instrs[0],
            Instruction::LoadTemp {
                array_idx: 0,
                idx: 0
            }
        );
    }

    #[test]
    fn compile_block_param_not_captured() {
        let code = compile_source("[ | x | x ]");
        let block_code = find_code_const(&code.constants);
        assert_eq!(block_code.arg_count, 1);
        assert_eq!(block_code.temp_count, 0);
        let instrs = decode(block_code);
        assert_eq!(
            instrs,
            vec![Instruction::LoadLocal { reg: 1 }, Instruction::LocalReturn,]
        );
    }

    #[test]
    fn compile_block_param_captured() {
        let code = compile_source("[ | x | [ x ] ]");
        let block_code = find_code_const(&code.constants);
        assert_eq!(block_code.arg_count, 1);
        assert_eq!(block_code.temp_count, 1);
        let block_instrs = decode(block_code);
        assert!(matches!(
            block_instrs[0],
            Instruction::MovToTemp {
                array_idx: 0,
                idx: 0,
                src: 1
            }
        ));

        let inner_code = find_code_const(&block_code.constants);
        let inner_instrs = decode(inner_code);
        assert_eq!(
            inner_instrs[0],
            Instruction::LoadTemp {
                array_idx: 0,
                idx: 0
            }
        );
    }

    #[test]
    fn compile_block_assignment_updates_capture() {
        let code = compile_source("[ x := 0. [ x := 1 ] ]");
        let outer_block = find_code_const(&code.constants);
        let inner_block = find_code_const(&outer_block.constants);
        let instrs = decode(inner_block);
        assert!(instrs.iter().any(|i| {
            matches!(
                i,
                Instruction::StoreTemp {
                    array_idx: 0,
                    idx: 0
                }
            )
        }));
    }

    #[test]
    fn compile_assignment_to_constant_is_error() {
        let exprs = parse_source("[ x = 1. x := 2 ]");
        let err = Compiler::compile(&exprs).expect_err("expected error");
        assert!(err.message.contains("cannot assign to constant"));
    }

    #[test]
    fn const_slot_initializer_with_local_uses_runtime_value_slot() {
        let code = compile_source("[ | s | { size = s } ]");
        let block_code = find_code_const_by_args(&code.constants, 1);
        let instrs = decode(block_code);
        assert!(instrs
            .iter()
            .any(|i| matches!(i, Instruction::CreateObject { .. })));
        let map_desc = block_code
            .constants
            .iter()
            .find_map(|c| match c {
                ConstEntry::Map(m) => Some(m),
                _ => None,
            })
            .expect("expected map constant in method code");
        let size_slot = map_desc
            .slots
            .iter()
            .find(|s| s.name == "size")
            .expect("size slot");
        assert!(size_slot.flags & SLOT_ASSIGNABLE != 0);
        assert!(size_slot.flags & SLOT_CONSTANT == 0);
    }

    #[test]
    fn top_level_const_assigns_assoc() {
        let code = compile_source("Math = { foo = { 1 }. }. Math foo");
        let instrs = decode(&code);
        assert!(instrs
            .iter()
            .any(|i| matches!(i, Instruction::StoreAssoc { .. })));
        assert!(instrs
            .iter()
            .any(|i| matches!(i, Instruction::LoadAssoc { .. })));
    }

    #[test]
    fn top_level_const_uses_assoc_constant() {
        let code = compile_source("Boolean = { }. Boolean");
        assert!(code.constants.iter().any(|c| {
            matches!(c, ConstEntry::Symbol(name) if name == "Boolean")
        }));
    }

    #[test]
    fn data_object_with_method_slot_includes_slot() {
        let code = compile_source("Math = { foo = { 1 }. }.");
        let map = code
            .constants
            .iter()
            .find_map(|c| match c {
                ConstEntry::Map(desc) => Some(desc),
                _ => None,
            })
            .expect("expected map constant");
        assert!(map.slots.iter().any(|s| s.name == "foo"));
    }

    #[test]
    fn top_level_const_emits_create_object() {
        let code = compile_source("Math = { foo = { 1 }. }.");
        let instrs = decode(&code);
        assert!(instrs
            .iter()
            .any(|i| matches!(i, Instruction::CreateObject { .. })));
    }

    #[test]
    fn top_level_const_create_before_store_assoc() {
        let code = compile_source("Math = { foo = { 1 }. }.");
        let instrs = decode(&code);
        let create_idx = instrs
            .iter()
            .position(|i| matches!(i, Instruction::CreateObject { .. }))
            .expect("missing create_object");
        let store_idx = instrs
            .iter()
            .position(|i| matches!(i, Instruction::StoreAssoc { .. }))
            .expect("missing store_assoc");
        assert!(create_idx < store_idx);
    }

    #[test]
    fn top_level_const_store_assoc_uses_create_result() {
        let code = compile_source("Math = { foo = { 1 }. }.");
        let instrs = decode(&code);
        let store_idx = instrs
            .iter()
            .position(|i| matches!(i, Instruction::StoreAssoc { .. }))
            .expect("missing store_assoc");
        assert!(store_idx > 0);
        assert!(matches!(
            instrs[store_idx - 1],
            Instruction::CreateObject { .. }
        ));
    }

    #[test]
    fn store_assoc_points_to_assoc_constant() {
        let code = compile_source("Math = { foo = { 1 }. }.");
        let instrs = decode(&code);
        let idx = instrs
            .iter()
            .find_map(|i| match i {
                Instruction::StoreAssoc { idx } => Some(*idx as usize),
                _ => None,
            })
            .expect("missing store_assoc");
        assert!(matches!(code.constants[idx], ConstEntry::Symbol(_)));
    }

    #[test]
    fn method_block_captures_local() {
        let code = compile_source("Obj = { foo = { x = 1. [ x ] call } }.");
        let map = code
            .constants
            .iter()
            .find_map(|c| match c {
                ConstEntry::Map(desc) => Some(desc),
                _ => None,
            })
            .expect("expected map constant");
        let mut method_code = None;
        for slot in &map.slots {
            if slot.name == "foo" {
                if let SlotValue::Constant(ConstEntry::Code(code)) = &slot.value
                {
                    method_code = Some(code);
                }
            }
        }
        let method_code = method_code.expect("expected foo code");
        let instrs = decode(method_code);
        assert!(instrs
            .iter()
            .any(|i| matches!(i, Instruction::StoreTemp { .. })));
        let block_code = find_code_const(&method_code.constants);
        let block_instrs = decode(block_code);
        assert!(block_instrs
            .iter()
            .any(|i| matches!(i, Instruction::LoadTemp { .. })));
    }

    #[test]
    fn compile_block_inherits_self() {
        let code = compile_source("[ self ]");
        let block_code = find_code_const(&code.constants);
        let instrs = decode(block_code);
        assert_eq!(
            instrs,
            vec![Instruction::LoadLocal { reg: 0 }, Instruction::LocalReturn,]
        );
    }

    #[test]
    fn compile_method_captures_param_and_local() {
        let code = compile_source("{ do: x With: y = { z = x. [ y + z ] } }");
        let method_code = find_code_const_by_args(&code.constants, 2);
        assert_eq!(method_code.temp_count, 2);

        let method_instrs = decode(method_code);
        assert!(method_instrs.iter().any(|i| {
            matches!(i, Instruction::MovToTemp { idx: 0, src: 2, .. })
        }));
        let inner_code = find_code_const(&method_code.constants);
        let inner_instrs = decode(inner_code);
        let mut load_temps = inner_instrs
            .iter()
            .filter(|i| matches!(i, Instruction::LoadTemp { .. }));
        let first = load_temps.next().expect("missing LoadTemp");
        let second = load_temps.next().expect("missing LoadTemp");
        assert!(matches!(first, Instruction::LoadTemp { idx: 0, .. }));
        assert!(matches!(second, Instruction::LoadTemp { idx: 1, .. }));
    }

    #[test]
    fn compile_block_inside_keyword_arg_captures_method_params() {
        let code = compile_source(
            "{ test: a B: b C: c = { out := True ifTrue: [ Target f: a B: b C: c ] IfFalse: [ 0 ]. out } }",
        );
        let method_code = find_code_const_by_args(&code.constants, 3);
        let mut saw_capture_inits = 0;
        for instr in decode(method_code) {
            if matches!(instr, Instruction::MovToTemp { .. }) {
                saw_capture_inits += 1;
            }
        }
        let block_code = find_code_const(&method_code.constants);
        let block_instrs = decode(block_code);
        assert!(saw_capture_inits >= 3, "expected captures for a,b,c");
        let load_temp_count = block_instrs
            .iter()
            .filter(|i| matches!(i, Instruction::LoadTemp { .. }))
            .count();
        assert!(
            load_temp_count >= 3,
            "expected block to load captured params from temps"
        );
        let assoc_loads: Vec<u16> = block_instrs
            .iter()
            .filter_map(|i| match i {
                Instruction::LoadAssoc { idx } => Some(*idx),
                _ => None,
            })
            .collect();
        assert_eq!(assoc_loads.len(), 1, "only Target should be global");
        let target_idx = assoc_loads[0] as usize;
        assert!(matches!(
            block_code.constants.get(target_idx),
            Some(ConstEntry::Symbol(s)) if s == "Target"
        ));
    }

    #[test]
    fn compile_keyword_method_uses_param_regs_in_keyword_send_args() {
        let code = compile_source(
            "{ test: path Flags: flags Mode: mode = { Posix open: path Flags: flags Mode: mode } }",
        );
        let method_code = find_code_const_by_args(&code.constants, 3);
        let instrs = decode(method_code);

        let mut saw_open_send = false;
        for (i, instr) in instrs.iter().enumerate() {
            if let Instruction::Send {
                message_idx,
                reg,
                argc,
                ..
            } = instr
            {
                let Some(ConstEntry::Symbol(sel)) =
                    method_code.constants.get(*message_idx as usize)
                else {
                    continue;
                };
                if sel == "open:Flags:Mode:" {
                    saw_open_send = true;
                    assert_eq!(*argc, 3);
                    // Receiver temp then three arg temps should be contiguous.
                    assert_eq!(*reg, 5);
                    assert!(matches!(
                        instrs.get(i.wrapping_sub(7)),
                        Some(Instruction::LoadLocal { reg: 1 })
                    ));
                    assert!(matches!(
                        instrs.get(i.wrapping_sub(6)),
                        Some(Instruction::StoreLocal { reg: 5 })
                    ));
                    assert!(matches!(
                        instrs.get(i.wrapping_sub(5)),
                        Some(Instruction::LoadLocal { reg: 2 })
                    ));
                    assert!(matches!(
                        instrs.get(i.wrapping_sub(4)),
                        Some(Instruction::StoreLocal { reg: 6 })
                    ));
                    assert!(matches!(
                        instrs.get(i.wrapping_sub(3)),
                        Some(Instruction::LoadLocal { reg: 3 })
                    ));
                    assert!(matches!(
                        instrs.get(i.wrapping_sub(2)),
                        Some(Instruction::StoreLocal { reg: 7 })
                    ));
                }
            }
        }

        assert!(saw_open_send, "expected open:Flags:Mode: send in method");
    }

    // ── Milestone 5: Globals + Cascade ──────────────────────────

    #[test]
    fn compile_global_ident() {
        let code = compile_source("Console");
        let instrs = decode(&code);
        assert_eq!(
            instrs,
            vec![Instruction::LoadAssoc { idx: 0 }, Instruction::LocalReturn,]
        );
        assert!(
            matches!(&code.constants[0], ConstEntry::Symbol(s) if s == "Console")
        );
    }

    #[test]
    fn compile_cascade() {
        let code = compile_source("3 factorial; print");
        let instrs = decode(&code);
        // Compile receiver (3), save to tmp
        assert_eq!(instrs[0], Instruction::LoadSmi { value: 3 });
        assert_eq!(instrs[1], Instruction::StoreLocal { reg: 1 }); // save recv

        // First cascade message: load recv, send factorial
        assert_eq!(instrs[2], Instruction::LoadLocal { reg: 1 });
        assert!(matches!(instrs[3], Instruction::Send { argc: 0, .. }));

        // Second cascade message: load recv, send print
        assert_eq!(instrs[4], Instruction::LoadLocal { reg: 1 });
        assert!(matches!(instrs[5], Instruction::Send { argc: 0, .. }));
    }

    #[test]
    fn compile_resend_unary() {
        let code = compile_source("resend self foo");
        let instrs = decode(&code);
        assert!(matches!(instrs[0], Instruction::Resend { argc: 0, .. }));
    }

    #[test]
    fn compile_directed_resend() {
        let code = compile_source("resend parent foo");
        let instrs = decode(&code);
        assert!(matches!(
            instrs[0],
            Instruction::DirectedResend { argc: 0, .. }
        ));
    }

    // ── Register allocation ─────────────────────────────────────

    #[test]
    fn registers_reused_across_statements() {
        let code = compile_source("1 + 2. 3 + 4");
        // Both binary messages should use the same temp registers
        // because they're in separate statements
        assert!(code.register_count <= 4); // self + 2 temps (reused) + some margin
    }

    #[test]
    fn constant_pool_deduplication() {
        let code = compile_source("x + x");
        // The symbol "+" should appear only once
        let symbol_count = code
            .constants
            .iter()
            .filter(|c| matches!(c, ConstEntry::Symbol(s) if s == "+"))
            .count();
        assert_eq!(symbol_count, 1);
    }

    // ── Integration ─────────────────────────────────────────────

    #[test]
    fn compile_complex_expression() {
        // Just verify it doesn't panic
        let _code = compile_source("x = 5. y = x + 3. y factorial");
    }

    #[test]
    fn compile_nested_message() {
        // (5 + 3) factorial
        let _code = compile_source("(5 + 3) factorial");
    }

    #[test]
    fn compile_unary_chain() {
        let code = compile_source("5 factorial print");
        let instrs = decode(&code);
        // 5 factorial → Send factorial
        // result print → Send print
        assert_eq!(instrs[0], Instruction::LoadSmi { value: 5 });
        assert!(matches!(instrs[1], Instruction::Send { argc: 0, .. }));
        assert!(matches!(instrs[2], Instruction::Send { argc: 0, .. }));
    }

    #[test]
    fn minimal_repro_trailing_ident_no_longer_clobbers_captured_temp() {
        let code = compile_source(
            "Obj = { m = { out := 1. i := 0. [ i < 1 ] whileTrue: [ out := out + 1. i := i + 1 ]. out } }.",
        );
        let method_code = find_slot_code_const(&code.constants, "m");
        let instrs = decode(method_code);

        // `out := 1` initializes one captured temp index.
        let out_idx = instrs
            .iter()
            .enumerate()
            .find_map(|(i, instr)| match instr {
                Instruction::StoreTemp { array_idx: 0, idx }
                    if i > 0
                        && matches!(
                            instrs[i - 1],
                            Instruction::LoadSmi { value: 1 }
                        ) =>
                {
                    Some(*idx)
                }
                _ => None,
            })
            .expect("expected out init store temp");

        // Regression guard: trailing `out` must be parsed as body expression,
        // so no `None` store should clobber the captured temp.
        let has_none_clobber = instrs.windows(2).any(|w| {
            matches!(
                w,
                [
                    Instruction::LoadAssoc { .. },
                    Instruction::StoreTemp {
                        array_idx: 0,
                        idx
                    }
                ] if *idx == out_idx
            )
        });

        assert!(
            !has_none_clobber,
            "unexpected LoadAssoc(None) + StoreTemp clobber on captured out"
        );
    }

    #[test]
    fn block_form_with_same_loop_shape_has_no_none_clobber() {
        let code = compile_source(
            "[ out := 1. i := 0. [ i < 1 ] whileTrue: [ out := out + 1. i := i + 1 ]. out ]",
        );
        let block_code = find_code_const(&code.constants);
        let instrs = decode(block_code);

        let has_none_store_to_temp = instrs.windows(2).any(|w| {
            matches!(
                w,
                [Instruction::LoadAssoc { .. }, Instruction::StoreTemp { .. }]
            )
        });

        assert!(
            !has_none_store_to_temp,
            "standalone block should not inject None into captured temps"
        );
    }

    // ── Helper ──────────────────────────────────────────────────

    fn find_code_const(constants: &[ConstEntry]) -> &CodeDesc {
        for c in constants {
            if let ConstEntry::Code(code) = c {
                return code;
            }
        }
        panic!("no Code constant found");
    }

    fn find_code_const_by_args(
        constants: &[ConstEntry],
        arg_count: u16,
    ) -> &CodeDesc {
        fn search<'a>(
            entry: &'a ConstEntry,
            arg_count: u16,
        ) -> Option<&'a CodeDesc> {
            match entry {
                ConstEntry::Code(code) => {
                    if code.arg_count == arg_count {
                        Some(code)
                    } else {
                        None
                    }
                }
                ConstEntry::Map(map) => {
                    for slot in &map.slots {
                        if let SlotValue::Constant(c) = &slot.value {
                            if let Some(found) = search(c, arg_count) {
                                return Some(found);
                            }
                        }
                    }
                    None
                }
                _ => None,
            }
        }

        for c in constants {
            if let Some(found) = search(c, arg_count) {
                return found;
            }
        }
        panic!("no Code constant found with arg_count {arg_count}");
    }

    fn find_slot_code_const<'a>(
        constants: &'a [ConstEntry],
        slot_name: &str,
    ) -> &'a CodeDesc {
        for c in constants {
            if let ConstEntry::Map(map) = c {
                for slot in &map.slots {
                    if slot.name == slot_name {
                        if let SlotValue::Constant(ConstEntry::Code(code)) =
                            &slot.value
                        {
                            return code;
                        }
                    }
                }
            }
        }
        panic!("no code constant found for slot {slot_name}");
    }
}
