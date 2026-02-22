use std::alloc::Layout;
use std::collections::HashMap;
use std::ptr;
use std::sync::Arc;

use heap::{HeapProxy, RootProvider};
use object::{
    code_allocation_size, init_code, init_map, init_str, init_symbol,
    map_allocation_size, Code, Map, MapFlags, Slot, SlotFlags, SlotObject,
    VMString, VMSymbol, Value,
};

use crate::alloc::{
    add_constant_slot, alloc_array, alloc_bignum_from_i128, alloc_byte_array,
    alloc_float, alloc_map, alloc_slot_object,
};
use crate::compiler0::{CodeDesc, ConstEntry, MapDesc, SlotValue};
use crate::{SharedVMData, VM};

// ── Root management ─────────────────────────────────────────────────

struct MaterializeRoots<'a> {
    scratch: Vec<Value>,
    intern_table: &'a mut HashMap<String, Value>,
}

impl RootProvider for MaterializeRoots<'_> {
    fn visit_roots(&mut self, visitor: &mut dyn FnMut(&mut Value)) {
        for v in &mut self.scratch {
            visitor(v);
        }
        for v in self.intern_table.values_mut() {
            visitor(v);
        }
    }
}

// ── Environment ─────────────────────────────────────────────────────

struct MaterializeEnv<'a, 'b> {
    proxy: &'a mut HeapProxy,
    roots: &'a mut MaterializeRoots<'b>,
    shared: Arc<SharedVMData>,
    // Indices into roots.scratch for well-known values
    none_idx: usize,
    map_map_idx: usize,
    assoc_map_idx: usize,
    dictionary_idx: usize,
}

impl<'a, 'b> MaterializeEnv<'a, 'b> {
    fn none(&self) -> Value {
        self.roots.scratch[self.none_idx]
    }

    fn map_map(&self) -> Value {
        self.roots.scratch[self.map_map_idx]
    }

    fn assoc_map(&self) -> Value {
        self.roots.scratch[self.assoc_map_idx]
    }

    fn dictionary(&self) -> Value {
        self.roots.scratch[self.dictionary_idx]
    }

    // ── Materialization entry point ──────────────────────────────

    fn materialize_code(&mut self, desc: &CodeDesc) -> Value {
        // Materialize each constant, storing the result in scratch.
        // Track scratch indices for each materialized constant.
        let base = self.roots.scratch.len();
        let mut materialized: Vec<usize> =
            Vec::with_capacity(desc.constants.len());

        for entry in &desc.constants {
            let val = self.materialize_const(entry, &materialized);
            let idx = self.roots.scratch.len();
            self.roots.scratch.push(val);
            materialized.push(idx);
        }

        // Collect the materialized values (re-read from scratch since GC
        // may have moved them).
        let constants: Vec<Value> = materialized
            .iter()
            .map(|&idx| self.roots.scratch[idx])
            .collect();

        // Allocate the Code object
        let constant_count = constants.len() as u32;
        let bytecode_len = desc.bytecode.len() as u32;
        let source_map_len =
            desc.source_map.len().min(u16::MAX as usize) as u16;
        let feedback_idx = self.roots.scratch.len();
        self.roots.scratch.push(self.none());
        if desc.feedback_count > 0 {
            let feedback = vec![self.none(); desc.feedback_count as usize];
            self.roots.scratch[feedback_idx] = unsafe {
                alloc_array(self.proxy, self.roots, &feedback).value()
            };
        }
        let size = code_allocation_size(
            constant_count,
            bytecode_len,
            source_map_len as u32,
        );
        let layout = Layout::from_size_align(size, 8).unwrap();
        let ptr = self.proxy.allocate(layout, self.roots);

        unsafe {
            let code_ptr = ptr.as_ptr() as *mut Code;
            init_code(
                code_ptr,
                constant_count,
                desc.register_count,
                desc.arg_count,
                bytecode_len,
                desc.temp_count,
                source_map_len,
                self.roots.scratch[feedback_idx],
            );

            // Re-read constants from scratch after allocation (GC safety)
            if !constants.is_empty() {
                let consts_dst = code_ptr.add(1) as *mut Value;
                for (i, &scratch_idx) in materialized.iter().enumerate() {
                    *consts_dst.add(i) = self.roots.scratch[scratch_idx];
                }
            }

            let bc_dst =
                (code_ptr.add(1) as *mut Value).add(constants.len()) as *mut u8;

            if !desc.bytecode.is_empty() {
                ptr::copy_nonoverlapping(
                    desc.bytecode.as_ptr(),
                    bc_dst,
                    desc.bytecode.len(),
                );
            }

            if source_map_len > 0 {
                let sm_dst = bc_dst.add(desc.bytecode.len());
                ptr::copy_nonoverlapping(
                    desc.source_map.as_ptr(),
                    sm_dst,
                    source_map_len as usize,
                );
            }

            let result = Value::from_ptr(code_ptr);

            // Clean up scratch (remove the temporaries we added)
            self.roots.scratch.truncate(base);

            result
        }
    }

    fn materialize_const(
        &mut self,
        entry: &ConstEntry,
        materialized: &[usize],
    ) -> Value {
        match entry {
            ConstEntry::Fixnum(n) => Value::from_i64(*n),
            ConstEntry::BigInt(n) => {
                let tagged = unsafe {
                    alloc_bignum_from_i128(self.proxy, self.roots, *n)
                };
                tagged.value()
            }
            ConstEntry::Float(f) => {
                let tagged = unsafe { alloc_float(self.proxy, self.roots, *f) };
                tagged.value()
            }
            ConstEntry::String(s) => self.alloc_str_value(s.as_bytes()),
            ConstEntry::Value(value) => *value,
            ConstEntry::Symbol(s) => self.intern(s),
            ConstEntry::ModuleAssoc { module, name } => {
                self.resolve_module_assoc(module, name)
            }
            ConstEntry::ModuleAssocValue { module, name } => {
                self.resolve_module_assoc_value(module, name)
            }
            ConstEntry::Code(desc) => self.materialize_code(desc),
            ConstEntry::Method { code, tail_call } => {
                let code_val = self.materialize_code(code);
                self.materialize_method(code_val, *tail_call)
            }
            ConstEntry::Map(desc) => self.materialize_map(desc, materialized),
        }
    }

    fn materialize_method(&mut self, code: Value, tail_call: bool) -> Value {
        let mut flags = MapFlags::HAS_CODE;
        if tail_call {
            flags = flags.with(MapFlags::TAIL_CALL);
        }
        let map_map = self.map_map();
        unsafe {
            let map_val =
                alloc_map(self.proxy, self.roots, map_map, code, flags, &[], 0)
                    .value();

            alloc_slot_object(self.proxy, self.roots, map_val, &[]).value()
        }
    }

    fn materialize_map(
        &mut self,
        desc: &MapDesc,
        materialized: &[usize],
    ) -> Value {
        // Resolve the code reference (if any)
        let code = match desc.code {
            Some(idx) => self.roots.scratch[materialized[idx]],
            None => self.none(),
        };
        let flags = if desc.code.is_some() {
            let mut flags = MapFlags::HAS_CODE;
            if desc.tail_call {
                flags = flags.with(MapFlags::TAIL_CALL);
            }
            flags
        } else {
            MapFlags::NONE
        };

        // Build slot array
        let mut slots: Vec<Slot> = Vec::with_capacity(desc.slots.len());
        for slot_desc in &desc.slots {
            let name = self.intern(&slot_desc.name);
            let value = match &slot_desc.value {
                SlotValue::Constant(entry) => {
                    self.materialize_const(entry, materialized)
                }
                SlotValue::Offset(off) => Value::from_i64(*off as i64),
            };
            slots.push(Slot::new(SlotFlags(slot_desc.flags), name, value));
        }

        // Allocate the Map
        let slot_count = slots.len() as u32;

        let size = map_allocation_size(slot_count);
        let layout = Layout::from_size_align(size, 8).unwrap();
        let ptr = self.proxy.allocate(layout, self.roots);

        unsafe {
            let map_ptr = ptr.as_ptr() as *mut Map;
            // Re-read map_map after allocation
            let mm = self.map_map();
            init_map(map_ptr, mm, code, flags, slot_count, desc.value_count);

            if !slots.is_empty() {
                let slots_dst = map_ptr.add(1) as *mut Slot;
                ptr::copy_nonoverlapping(
                    slots.as_ptr(),
                    slots_dst,
                    slots.len(),
                );
            }

            Value::from_ptr(map_ptr)
        }
    }

    // ── Assoc resolution ─────────────────────────────────────────

    fn resolve_assoc(&mut self, name: &str) -> Value {
        // Look up the name in the dictionary's map slots
        let sym = self.intern(name);
        let sym_idx = self.roots.scratch.len();
        self.roots.scratch.push(sym);

        let dict = self.dictionary();
        unsafe {
            let dict_obj: &SlotObject = dict.as_ref();
            let map: &Map = dict_obj.map.as_ref();
            let slots = map.slots();

            for slot in slots {
                if slot.name.raw() == self.roots.scratch[sym_idx].raw() {
                    let assoc = slot.value;
                    self.roots.scratch.pop();
                    return assoc;
                }
            }
        }

        // Not found — create a new assoc and grow the dictionary
        let assoc = self.create_assoc();
        let assoc_idx = self.roots.scratch.len();
        self.roots.scratch.push(assoc);

        self.grow_dictionary(assoc_idx, sym_idx);

        let result = assoc;
        // Clean up: remove assoc and sym from scratch
        // sym_idx < assoc_idx, so remove assoc first
        self.roots.scratch.pop(); // assoc
        self.roots.scratch.pop(); // sym
        result
    }

    fn resolve_module_assoc(&mut self, module: &str, name: &str) -> Value {
        if let Some(cell) =
            self.shared.modules.lock().ok().and_then(|modules| {
                modules
                    .get(module)
                    .and_then(|m| m.bindings.get(name))
                    .copied()
            })
        {
            return cell;
        }

        let assoc = self.resolve_assoc(&format!("{module}::{name}"));
        if let Ok(mut modules) = self.shared.modules.lock() {
            let module_state = modules.entry(module.to_string()).or_default();
            module_state.bindings.insert(name.to_string(), assoc);
        }
        assoc
    }

    fn resolve_module_assoc_value(
        &mut self,
        module: &str,
        name: &str,
    ) -> Value {
        let assoc = self.resolve_module_assoc(module, name);
        let assoc_obj: &SlotObject = unsafe { assoc.as_ref() };
        unsafe { assoc_obj.read_value(SlotObject::VALUES_OFFSET) }
    }

    fn create_assoc(&mut self) -> Value {
        // An assoc is a SlotObject with assoc_map and one inline value (None)
        let size = object::slot_object_allocation_size(1);
        let layout = Layout::from_size_align(size, 8).unwrap();
        let ptr = self.proxy.allocate(layout, self.roots);

        unsafe {
            let obj_ptr = ptr.as_ptr() as *mut SlotObject;
            // Re-read assoc_map and None after allocation (GC safety)
            let am = self.assoc_map();
            let n = self.none();
            ptr::write(
                obj_ptr,
                SlotObject {
                    header: object::Header::new(object::ObjectType::Slots),
                    map: am,
                },
            );
            // Write the inline value (None)
            let vals_dst = obj_ptr.add(1) as *mut Value;
            *vals_dst = n;

            Value::from_ptr(obj_ptr)
        }
    }

    fn grow_dictionary(&mut self, assoc_idx: usize, sym_idx: usize) {
        unsafe {
            let dict = self.dictionary();
            let dict_obj: &SlotObject = dict.as_ref();
            let old_map = dict_obj.map;
            let map_map = self.map_map();
            let sym = self.roots.scratch[sym_idx];
            let assoc = self.roots.scratch[assoc_idx];

            let new_map = add_constant_slot(
                self.proxy, self.roots, old_map, map_map, sym, assoc,
            );

            // Re-read dictionary from scratch (GC may have moved it)
            let dict_val = self.dictionary();
            let dict_obj_mut = &mut *(dict_val.ref_bits() as *mut SlotObject);
            dict_obj_mut.map = new_map;
        }
    }

    // ── Symbol interning ─────────────────────────────────────────

    fn intern(&mut self, name: &str) -> Value {
        if let Some(&val) = self.roots.intern_table.get(name) {
            return val;
        }
        let sym_val = self.alloc_symbol_value(name.as_bytes());
        self.roots.intern_table.insert(name.to_string(), sym_val);
        sym_val
    }

    fn alloc_str_value(&mut self, content: &[u8]) -> Value {
        // Allocate ByteArray: content + NUL terminator
        let mut bytes = Vec::with_capacity(content.len() + 1);
        bytes.extend_from_slice(content);
        bytes.push(0); // NUL terminator

        let ba = unsafe { alloc_byte_array(self.proxy, self.roots, &bytes) };
        let ba_val = ba.value();

        // Root the ByteArray before allocating VMString
        let ba_idx = self.roots.scratch.len();
        self.roots.scratch.push(ba_val);

        // Allocate VMString
        let size = size_of::<VMString>();
        let layout = Layout::from_size_align(size, 8).unwrap();
        let ptr = self.proxy.allocate(layout, self.roots);

        unsafe {
            let str_ptr = ptr.as_ptr() as *mut VMString;
            // Re-read BA from scratch after allocation
            let ba = self.roots.scratch[ba_idx];
            init_str(str_ptr, content.len() as u64, ba);
            let result = Value::from_ptr(str_ptr);

            // Clean up scratch
            self.roots.scratch.pop();

            result
        }
    }

    fn alloc_symbol_value(&mut self, content: &[u8]) -> Value {
        let mut bytes = Vec::with_capacity(content.len() + 1);
        bytes.extend_from_slice(content);
        bytes.push(0);

        let ba = unsafe { alloc_byte_array(self.proxy, self.roots, &bytes) };
        let ba_val = ba.value();

        let ba_idx = self.roots.scratch.len();
        self.roots.scratch.push(ba_val);

        let size = size_of::<VMSymbol>();
        let layout = Layout::from_size_align(size, 8).unwrap();
        let ptr = self.proxy.allocate(layout, self.roots);

        unsafe {
            let sym_ptr = ptr.as_ptr() as *mut VMSymbol;
            let ba = self.roots.scratch[ba_idx];
            init_symbol(sym_ptr, content.len() as u64, ba);
            let result = Value::from_ptr(sym_ptr);
            self.roots.scratch.pop();
            result
        }
    }
}

// ── Public API ──────────────────────────────────────────────────────

/// Materialize a [`CodeDesc`] into a live heap [`Code`] object, resolving
/// all constants (symbols, assocs, nested code/maps) against the VM's
/// dictionary and intern table.
pub fn materialize(vm: &mut VM, desc: &CodeDesc) -> Value {
    let shared = vm.shared.clone();
    // Snapshot VM specials into scratch so they survive GC
    let mut scratch = Vec::with_capacity(32);

    let none_idx = scratch.len();
    scratch.push(vm.special.none);

    let map_map_idx = scratch.len();
    scratch.push(vm.special.map_map);

    let assoc_map_idx = scratch.len();
    scratch.push(vm.assoc_map);

    let dictionary_idx = scratch.len();
    scratch.push(vm.dictionary);

    // Also root all other specials (indices 4..16)
    scratch.push(vm.special.string_traits); // 4
    scratch.push(vm.special.symbol_traits); // 5
    scratch.push(vm.special.true_obj); // 6
    scratch.push(vm.special.false_obj); // 7
    scratch.push(vm.special.array_traits); // 8
    scratch.push(vm.special.bytearray_traits); // 9
    scratch.push(vm.special.bignum_traits); // 10
    scratch.push(vm.special.alien_traits); // 11
    scratch.push(vm.special.ratio_traits); // 12
    scratch.push(vm.special.fixnum_traits); // 13
    scratch.push(vm.special.code_traits); // 14
    scratch.push(vm.special.float_traits); // 15
    scratch.push(vm.special.block_traits); // 16

    let mut intern_table = vm
        .shared
        .intern_table
        .lock()
        .expect("intern table poisoned");
    let mut roots = MaterializeRoots {
        scratch,
        intern_table: &mut intern_table,
    };

    let result = {
        let mut env = MaterializeEnv {
            proxy: &mut vm.heap_proxy,
            roots: &mut roots,
            shared,
            none_idx,
            map_map_idx,
            assoc_map_idx,
            dictionary_idx,
        };
        env.materialize_code(desc)
    };

    // Write back potentially-moved values to VM
    vm.special.none = roots.scratch[none_idx];
    vm.special.map_map = roots.scratch[map_map_idx];
    vm.assoc_map = roots.scratch[assoc_map_idx];
    vm.dictionary = roots.scratch[dictionary_idx];
    vm.special.string_traits = roots.scratch[4];
    vm.special.symbol_traits = roots.scratch[5];
    vm.special.true_obj = roots.scratch[6];
    vm.special.false_obj = roots.scratch[7];
    vm.special.array_traits = roots.scratch[8];
    vm.special.bytearray_traits = roots.scratch[9];
    vm.special.bignum_traits = roots.scratch[10];
    vm.special.alien_traits = roots.scratch[11];
    vm.special.ratio_traits = roots.scratch[12];
    vm.special.fixnum_traits = roots.scratch[13];
    vm.special.code_traits = roots.scratch[14];
    vm.special.float_traits = roots.scratch[15];
    vm.special.block_traits = roots.scratch[16];

    result
}

// ── Tests ───────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::compiler0::SlotDesc;
    use crate::special::bootstrap;
    use heap::HeapSettings;
    use object::{Array, Float, Header, ObjectType};

    fn test_settings() -> HeapSettings {
        HeapSettings {
            heap_size: 1024 * 1024,
            block_size: 8192,
            large_size: 4096 - 16,
            line_size: 64,
            bytes_before_gc: 0.1,
            nursery_fraction: 0.1,
            minor_recycle_threshold: 0.5,
            max_minor_before_major: 3,
        }
    }

    fn empty_bytecode() -> Vec<u8> {
        // A minimal bytecode: just LocalReturn (opcode 0x03)
        vec![0x03]
    }

    fn dict_slot_count(vm: &VM) -> u32 {
        unsafe {
            let dict: &SlotObject = vm.dictionary.as_ref();
            let map: &Map = dict.map.as_ref();
            map.slot_count()
        }
    }

    #[test]
    fn materialize_fixnum() {
        let mut vm = bootstrap(test_settings());
        let desc = CodeDesc {
            bytecode: empty_bytecode(),
            constants: vec![ConstEntry::Fixnum(42)],
            register_count: 1,
            arg_count: 0,
            temp_count: 0,
            feedback_count: 0,
            source_map: vec![],
        };
        let code_val = materialize(&mut vm, &desc);
        assert!(code_val.is_ref());
        unsafe {
            let code: &Code = code_val.as_ref();
            assert_eq!(code.constant_count(), 1);
            let c = code.constant(0);
            assert!(c.is_fixnum());
            assert_eq!(c.to_i64(), 42);
        }
    }

    #[test]
    fn materialize_float() {
        let mut vm = bootstrap(test_settings());
        let desc = CodeDesc {
            bytecode: empty_bytecode(),
            constants: vec![ConstEntry::Float(3.14)],
            register_count: 1,
            arg_count: 0,
            temp_count: 0,
            feedback_count: 0,
            source_map: vec![],
        };
        let code_val = materialize(&mut vm, &desc);
        unsafe {
            let code: &Code = code_val.as_ref();
            assert_eq!(code.constant_count(), 1);
            let c = code.constant(0);
            assert!(c.is_ref());
            let float: &Float = c.as_ref();
            assert_eq!(float.header.object_type(), object::ObjectType::Float);
            assert!((float.value - 3.14).abs() < 1e-10);
        }
    }

    #[test]
    fn materialize_bigint() {
        let mut vm = bootstrap(test_settings());
        let desc = CodeDesc {
            bytecode: empty_bytecode(),
            constants: vec![ConstEntry::BigInt(18_446_744_073_709_551_615)],
            register_count: 1,
            arg_count: 0,
            temp_count: 0,
            feedback_count: 0,
            source_map: vec![],
        };
        let code_val = materialize(&mut vm, &desc);
        unsafe {
            let code: &Code = code_val.as_ref();
            assert_eq!(code.constant_count(), 1);
            let c = code.constant(0);
            assert!(c.is_ref());
            let header: &Header = c.as_ref();
            assert_eq!(header.object_type(), ObjectType::BigNum);
        }
    }

    #[test]
    fn materialize_symbol() {
        let mut vm = bootstrap(test_settings());
        let desc = CodeDesc {
            bytecode: empty_bytecode(),
            constants: vec![ConstEntry::Symbol("hello".to_string())],
            register_count: 1,
            arg_count: 0,
            temp_count: 0,
            feedback_count: 0,
            source_map: vec![],
        };
        let code_val = materialize(&mut vm, &desc);
        unsafe {
            let code: &Code = code_val.as_ref();
            let c = code.constant(0);
            assert!(c.is_ref());
            let s: &VMString = c.as_ref();
            assert_eq!(s.as_str(), "hello");
        }
    }

    #[test]
    fn materialize_intern_dedup() {
        let mut vm = bootstrap(test_settings());
        let desc = CodeDesc {
            bytecode: empty_bytecode(),
            constants: vec![
                ConstEntry::Symbol("foo".to_string()),
                ConstEntry::Symbol("foo".to_string()),
            ],
            register_count: 1,
            arg_count: 0,
            temp_count: 0,
            feedback_count: 0,
            source_map: vec![],
        };
        let code_val = materialize(&mut vm, &desc);
        unsafe {
            let code: &Code = code_val.as_ref();
            let c0 = code.constant(0);
            let c1 = code.constant(1);
            // Same pointer (interned)
            assert_eq!(c0.raw(), c1.raw());
        }
    }

    #[test]
    fn materialize_assoc_creates() {
        let mut vm = bootstrap(test_settings());
        let base_slots = dict_slot_count(&vm);
        let desc = CodeDesc {
            bytecode: empty_bytecode(),
            constants: vec![ConstEntry::ModuleAssoc {
                module: "User".to_string(),
                name: "myGlobal".to_string(),
            }],
            register_count: 1,
            arg_count: 0,
            temp_count: 0,
            feedback_count: 0,
            source_map: vec![],
        };
        let code_val = materialize(&mut vm, &desc);
        unsafe {
            let code: &Code = code_val.as_ref();
            let value = code.constant(0);
            let assoc_obj: &SlotObject = value.as_ref();
            let assoc_val = assoc_obj.read_value(SlotObject::VALUES_OFFSET);
            assert_eq!(assoc_val.raw(), vm.special.none.raw());

            // Dictionary should have one additional slot now
            let dict: &SlotObject = vm.dictionary.as_ref();
            let map: &Map = dict.map.as_ref();
            assert_eq!(map.slot_count(), base_slots + 1);
            let mut found = false;
            let sym = vm
                .with_intern_table(|table| table.get("User::myGlobal").copied())
                .expect("interned User::myGlobal");
            for slot in map.slots() {
                if slot.name.raw() == sym.raw() {
                    found = true;
                    break;
                }
            }
            assert!(found, "assoc not found in dictionary");
        }
    }

    #[test]
    fn materialize_assoc_reuses() {
        let mut vm = bootstrap(test_settings());
        let base_slots = dict_slot_count(&vm);

        // First materialization creates the assoc
        let desc1 = CodeDesc {
            bytecode: empty_bytecode(),
            constants: vec![ConstEntry::ModuleAssoc {
                module: "User".to_string(),
                name: "shared".to_string(),
            }],
            register_count: 1,
            arg_count: 0,
            temp_count: 0,
            feedback_count: 0,
            source_map: vec![],
        };
        let code1 = materialize(&mut vm, &desc1);

        // Second materialization should reuse the same assoc
        let desc2 = CodeDesc {
            bytecode: empty_bytecode(),
            constants: vec![ConstEntry::ModuleAssoc {
                module: "User".to_string(),
                name: "shared".to_string(),
            }],
            register_count: 1,
            arg_count: 0,
            temp_count: 0,
            feedback_count: 0,
            source_map: vec![],
        };
        let code2 = materialize(&mut vm, &desc2);

        unsafe {
            let c1: &Code = code1.as_ref();
            let c2: &Code = code2.as_ref();
            let value1 = c1.constant(0);
            let value2 = c2.constant(0);
            assert_eq!(value1.raw(), value2.raw());

            // Dictionary should still have only one additional slot
            let dict: &SlotObject = vm.dictionary.as_ref();
            let map: &Map = dict.map.as_ref();
            assert_eq!(map.slot_count(), base_slots + 1);
        }
    }

    #[test]
    fn materialize_nested_code() {
        let mut vm = bootstrap(test_settings());
        let inner = CodeDesc {
            bytecode: empty_bytecode(),
            constants: vec![ConstEntry::Fixnum(99)],
            register_count: 1,
            arg_count: 0,
            temp_count: 0,
            feedback_count: 0,
            source_map: vec![],
        };
        let desc = CodeDesc {
            bytecode: empty_bytecode(),
            constants: vec![ConstEntry::Code(inner)],
            register_count: 1,
            arg_count: 0,
            temp_count: 0,
            feedback_count: 0,
            source_map: vec![],
        };
        let code_val = materialize(&mut vm, &desc);
        unsafe {
            let code: &Code = code_val.as_ref();
            let inner_val = code.constant(0);
            assert!(inner_val.is_ref());
            let inner_code: &Code = inner_val.as_ref();
            assert_eq!(inner_code.constant_count(), 1);
            let c = inner_code.constant(0);
            assert!(c.is_fixnum());
            assert_eq!(c.to_i64(), 99);
        }
    }

    #[test]
    fn materialize_code_feedback_vector() {
        let mut vm = bootstrap(test_settings());
        let desc = CodeDesc {
            bytecode: empty_bytecode(),
            constants: vec![],
            register_count: 1,
            arg_count: 0,
            temp_count: 0,
            feedback_count: 3,
            source_map: vec![],
        };

        let code_val = materialize(&mut vm, &desc);
        unsafe {
            let code: &Code = code_val.as_ref();
            assert!(code.feedback.is_ref());
            let feedback: &Array = code.feedback.as_ref();
            assert_eq!(feedback.len(), 3);
            for i in 0..feedback.len() {
                assert_eq!(feedback.element(i).raw(), vm.special.none.raw());
            }
        }
    }

    #[test]
    fn materialize_map() {
        let mut vm = bootstrap(test_settings());

        // Code constant at index 0, Map constant at index 1 that references it
        let inner_code = CodeDesc {
            bytecode: empty_bytecode(),
            constants: vec![],
            register_count: 1,
            arg_count: 0,
            temp_count: 0,
            feedback_count: 0,
            source_map: vec![],
        };
        let map_desc = MapDesc {
            slots: vec![SlotDesc {
                flags: SlotFlags::CONSTANT.0,
                name: "x".to_string(),
                value: SlotValue::Constant(ConstEntry::Fixnum(7)),
            }],
            value_count: 0,
            code: Some(0), // references constant[0]
            tail_call: false,
        };
        let desc = CodeDesc {
            bytecode: empty_bytecode(),
            constants: vec![
                ConstEntry::Code(inner_code),
                ConstEntry::Map(map_desc),
            ],
            register_count: 1,
            arg_count: 0,
            temp_count: 0,
            feedback_count: 0,
            source_map: vec![],
        };
        let code_val = materialize(&mut vm, &desc);
        unsafe {
            let code: &Code = code_val.as_ref();
            let map_val = code.constant(1);
            assert!(map_val.is_ref());
            let map: &Map = map_val.as_ref();
            assert_eq!(map.slot_count(), 1);
            assert_eq!(map.value_count(), 0);
            // Map's code field should reference the inner Code
            let code_ref = code.constant(0);
            assert_eq!(map.code.raw(), code_ref.raw());
            // Slot should have name "x" and value fixnum 7
            let slot = map.slot(0);
            assert!(slot.is_constant());
            assert_eq!(slot.value.to_i64(), 7);
        }
    }

    #[test]
    fn materialize_dictionary_growth() {
        let mut vm = bootstrap(test_settings());
        let base_slots = dict_slot_count(&vm);
        let desc = CodeDesc {
            bytecode: empty_bytecode(),
            constants: vec![
                ConstEntry::ModuleAssoc {
                    module: "User".to_string(),
                    name: "a".to_string(),
                },
                ConstEntry::ModuleAssoc {
                    module: "User".to_string(),
                    name: "b".to_string(),
                },
                ConstEntry::ModuleAssoc {
                    module: "User".to_string(),
                    name: "c".to_string(),
                },
            ],
            register_count: 1,
            arg_count: 0,
            temp_count: 0,
            feedback_count: 0,
            source_map: vec![],
        };
        let code_val = materialize(&mut vm, &desc);
        unsafe {
            let code: &Code = code_val.as_ref();
            let a = code.constant(0);
            let b = code.constant(1);
            let c = code.constant(2);
            let a_obj: &SlotObject = a.as_ref();
            let b_obj: &SlotObject = b.as_ref();
            let c_obj: &SlotObject = c.as_ref();
            let a_val = a_obj.read_value(SlotObject::VALUES_OFFSET);
            let b_val = b_obj.read_value(SlotObject::VALUES_OFFSET);
            let c_val = c_obj.read_value(SlotObject::VALUES_OFFSET);
            assert_eq!(a_val.raw(), vm.special.none.raw());
            assert_eq!(b_val.raw(), vm.special.none.raw());
            assert_eq!(c_val.raw(), vm.special.none.raw());

            // Dictionary should have 3 additional slots
            let dict: &SlotObject = vm.dictionary.as_ref();
            let map: &Map = dict.map.as_ref();
            assert_eq!(map.slot_count(), base_slots + 3);
        }
    }

    /// Minimal root provider for tests that need split-borrow of VM fields.
    struct TestRoots {
        values: Vec<Value>,
    }

    impl RootProvider for TestRoots {
        fn visit_roots(&mut self, visitor: &mut dyn FnMut(&mut Value)) {
            for v in &mut self.values {
                visitor(v);
            }
        }
    }

    #[test]
    fn add_constant_slot_works() {
        let mut vm = bootstrap(test_settings());
        let name = Value::from_i64(42);
        let value = Value::from_i64(99);

        unsafe {
            let map_map = vm.special.map_map;
            let none = vm.special.none;
            let mut roots = TestRoots {
                values: vec![map_map, none],
            };

            // Start with an empty map
            let (mm, n) = (roots.values[0], roots.values[1]);
            let empty_map = crate::alloc::alloc_map(
                &mut vm.heap_proxy,
                &mut roots,
                mm,
                n,
                MapFlags::NONE,
                &[],
                0,
            )
            .value();
            roots.values.push(empty_map);

            let (em, mm) = (roots.values[2], roots.values[0]);
            let new_map = add_constant_slot(
                &mut vm.heap_proxy,
                &mut roots,
                em,
                mm,
                name,
                value,
            );

            let map: &Map = new_map.as_ref();
            assert_eq!(map.slot_count(), 1);
            let slot = map.slot(0);
            assert!(slot.is_constant());
            assert_eq!(slot.name.raw(), name.raw());
            assert_eq!(slot.value.raw(), value.raw());
        }
    }

    #[test]
    fn remove_constant_slot_works() {
        let mut vm = bootstrap(test_settings());

        unsafe {
            let map_map = vm.special.map_map;
            let none = vm.special.none;
            let mut roots = TestRoots {
                values: vec![map_map, none],
            };

            let slots = [
                Slot::new(
                    SlotFlags::CONSTANT,
                    Value::from_i64(1),
                    Value::from_i64(10),
                ),
                Slot::new(
                    SlotFlags::CONSTANT,
                    Value::from_i64(2),
                    Value::from_i64(20),
                ),
                Slot::new(
                    SlotFlags::CONSTANT,
                    Value::from_i64(3),
                    Value::from_i64(30),
                ),
            ];

            let (mm, n) = (roots.values[0], roots.values[1]);
            let map_val = crate::alloc::alloc_map(
                &mut vm.heap_proxy,
                &mut roots,
                mm,
                n,
                MapFlags::NONE,
                &slots,
                0,
            )
            .value();
            roots.values.push(map_val);

            // Remove slot at index 1 (name=2, value=20)
            let (mv, mm) = (roots.values[2], roots.values[0]);
            let new_map = crate::alloc::remove_constant_slot(
                &mut vm.heap_proxy,
                &mut roots,
                mv,
                mm,
                1,
            );

            let map: &Map = new_map.as_ref();
            assert_eq!(map.slot_count(), 2);
            let s0 = map.slot(0);
            let s1 = map.slot(1);
            assert_eq!(s0.name.to_i64(), 1);
            assert_eq!(s0.value.to_i64(), 10);
            assert_eq!(s1.name.to_i64(), 3);
            assert_eq!(s1.value.to_i64(), 30);
        }
    }
}
