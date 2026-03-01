use std::collections::HashMap;

use compiler0::{CompileError, Compiler, ModuleSnapshot, ModuleSnapshotState};
use parser::ast::{AstArena, ExprId};

use crate::VM;

pub fn compile_for_vm_ids(
    vm: &VM,
    arena: &AstArena,
    exprs: &[ExprId],
) -> Result<compiler0::CodeDesc, CompileError> {
    let snapshot = build_module_snapshot(vm);
    Compiler::compile_with_module_snapshot_ids(&snapshot, arena, exprs)
}

fn build_module_snapshot(vm: &VM) -> ModuleSnapshot {
    let mut modules = HashMap::new();
    vm.with_modules(|loaded| {
        for (path, module) in loaded.iter() {
            let mut state = ModuleSnapshotState::default();
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
    });

    ModuleSnapshot {
        current_module: vm.current_module.clone(),
        modules,
    }
}
