pub mod alloc;
pub mod compiler0;
pub mod interpreter;
pub mod materialize;
pub mod primitives;
pub mod special;

use std::collections::{HashMap, HashSet};

use heap::{HeapProxy, RootProvider, SizeFn};
use libffi::middle::Cif;
use object::{
    Array, BigNum, Block, ByteArray, Code, Float, Header, HeaderFlags, Map,
    ObjectType, Ratio, SlotObject, SpecialObjects, VMString, VMSymbol, Value,
};

/// The VM owns a heap proxy and the bootstrapped special objects.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModuleImport {
    pub module_path: String,
    pub export_name: String,
}

#[derive(Debug, Default)]
pub struct ModuleState {
    pub bindings: HashMap<String, Value>,
    pub imports: HashMap<String, ModuleImport>,
    pub uses: Vec<String>,
    pub exports: HashSet<String>,
}

pub struct VM {
    pub heap_proxy: HeapProxy,
    pub special: SpecialObjects,
    /// Interned symbols: Rust string -> heap symbol Value.
    pub intern_table: HashMap<String, Value>,
    /// Registered primitive descriptors.
    pub primitives: Vec<primitives::PrimitiveDesc>,
    /// Shared map for all assoc objects (0 named slots, value_count=1).
    pub assoc_map: Value,
    /// Cached libffi call interfaces keyed by function signature.
    pub ffi_cif_cache: HashMap<primitives::alien::CifCacheKey, Cif>,
    /// The global dictionary object (SlotObject whose map has one CONSTANT
    /// slot per global).
    pub dictionary: Value,
    /// Currently open module path. `None` means legacy global dictionary mode.
    pub current_module: Option<String>,
    /// Runtime module registry.
    pub modules: HashMap<String, ModuleState>,
    /// Optional global assoc name to trace load/store.
    #[cfg(debug_assertions)]
    pub trace_assoc_name: Option<String>,
    /// Optional message selector to trace sends.
    #[cfg(debug_assertions)]
    pub trace_send_name: Option<String>,
}

impl RootProvider for VM {
    fn visit_roots(&mut self, visitor: &mut dyn FnMut(&mut Value)) {
        visitor(&mut self.special.none);
        visitor(&mut self.special.true_obj);
        visitor(&mut self.special.false_obj);
        visitor(&mut self.special.map_map);
        visitor(&mut self.special.object);
        visitor(&mut self.special.block_traits);
        visitor(&mut self.special.array_traits);
        visitor(&mut self.special.bytearray_traits);
        visitor(&mut self.special.bignum_traits);
        visitor(&mut self.special.alien_traits);
        visitor(&mut self.special.string_traits);
        visitor(&mut self.special.symbol_traits);
        visitor(&mut self.special.ratio_traits);
        visitor(&mut self.special.fixnum_traits);
        visitor(&mut self.special.code_traits);
        visitor(&mut self.special.float_traits);
        visitor(&mut self.special.mirror);
        visitor(&mut self.assoc_map);
        visitor(&mut self.dictionary);
        for module in self.modules.values_mut() {
            for value in module.bindings.values_mut() {
                visitor(value);
            }
        }
        for v in self.intern_table.values_mut() {
            visitor(v);
        }
    }
}

impl VM {
    fn module_resolve_read_target(
        &self,
        module_path: &str,
        name: &str,
        seen: &mut HashSet<(String, String)>,
    ) -> Option<(String, String)> {
        let key = (module_path.to_string(), name.to_string());
        if !seen.insert(key) {
            return None;
        }

        let module = self.modules.get(module_path)?;
        if module.bindings.contains_key(name) {
            return Some((module_path.to_string(), name.to_string()));
        }

        let import = module.imports.get(name)?;
        self.module_resolve_read_target(
            &import.module_path,
            &import.export_name,
            seen,
        )
    }

    fn module_resolve_write_target(
        &self,
        module_path: &str,
        name: &str,
        seen: &mut HashSet<(String, String)>,
    ) -> Option<(String, String)> {
        let key = (module_path.to_string(), name.to_string());
        if !seen.insert(key) {
            return None;
        }

        let module = self.modules.get(module_path)?;
        if let Some(import) = module.imports.get(name) {
            return self.module_resolve_write_target(
                &import.module_path,
                &import.export_name,
                seen,
            );
        }

        Some((module_path.to_string(), name.to_string()))
    }

    pub fn module_lookup_in(
        &self,
        module_path: &str,
        name: &str,
    ) -> Option<Value> {
        let mut seen = HashSet::new();
        let (owner_path, owner_name) =
            self.module_resolve_read_target(module_path, name, &mut seen)?;
        self.modules
            .get(&owner_path)
            .and_then(|m| m.bindings.get(&owner_name))
            .copied()
    }

    pub fn module_store_in(
        &mut self,
        module_path: &str,
        name: &str,
        value: Value,
    ) -> bool {
        self.ensure_module(module_path);

        let mut seen = HashSet::new();
        let (owner_path, owner_name) = self
            .module_resolve_write_target(module_path, name, &mut seen)
            .unwrap_or_else(|| (module_path.to_string(), name.to_string()));
        self.ensure_module(&owner_path);

        if let Some(module) = self.modules.get_mut(&owner_path) {
            module.bindings.insert(owner_name, value);
            true
        } else {
            false
        }
    }

    pub fn module_owner_of_value(&self, value: Value) -> Option<String> {
        if !value.is_ref() {
            return None;
        }

        for (path, module) in &self.modules {
            if module.bindings.values().any(|v| v.raw() == value.raw()) {
                return Some(path.clone());
            }
        }

        None
    }

    pub fn ensure_module(&mut self, path: &str) {
        self.modules.entry(path.to_string()).or_default();
    }

    pub fn seed_user_module_from_dictionary(&mut self) {
        self.ensure_module("user");
        let mut entries: Vec<(String, Value)> = Vec::new();

        if self.dictionary.is_ref() {
            unsafe {
                let dict: &SlotObject = self.dictionary.as_ref();
                let map: &Map = dict.map.as_ref();
                for slot in map.slots() {
                    if !slot.name.is_ref() {
                        continue;
                    }
                    let header: &Header = slot.name.as_ref();
                    if header.object_type() != ObjectType::Symbol {
                        continue;
                    }
                    let sym: &VMSymbol = slot.name.as_ref();
                    let binding_value = if slot.value.is_ref() {
                        let value_header: &Header = slot.value.as_ref();
                        if value_header.object_type() == ObjectType::Slots {
                            let assoc: &SlotObject = slot.value.as_ref();
                            assoc.read_value(SlotObject::VALUES_OFFSET)
                        } else {
                            slot.value
                        }
                    } else {
                        slot.value
                    };
                    entries.push((sym.as_str().to_string(), binding_value));
                }
            }
        }

        if let Some(user) = self.modules.get_mut("user") {
            for (name, value) in entries {
                user.bindings.insert(name.clone(), value);
                user.exports.insert(name);
            }
        }
    }

    pub fn open_module(&mut self, path: &str) {
        self.ensure_module(path);
        self.current_module = Some(path.to_string());
        if path != "user" {
            let _ = self.module_use("user", &HashMap::new());
        }
    }

    pub fn current_module_state(&self) -> Option<&ModuleState> {
        let path = self.current_module.as_ref()?;
        self.modules.get(path)
    }

    pub fn current_module_state_mut(&mut self) -> Option<&mut ModuleState> {
        let path = self.current_module.clone()?;
        self.modules.get_mut(&path)
    }

    pub fn module_store_current(&mut self, name: &str, value: Value) -> bool {
        let Some(current) = self.current_module.clone() else {
            return false;
        };
        self.module_store_in(&current, name, value)
    }

    pub fn module_lookup_current(&self, name: &str) -> Option<Value> {
        let current = self.current_module.as_ref()?;
        self.module_lookup_in(current, name)
    }

    pub fn module_export_current(&mut self, name: &str) -> Result<(), String> {
        let Some(path) = self.current_module.clone() else {
            return Err(
                "no current module; call Module open: first".to_string()
            );
        };
        self.ensure_module(&path);
        if let Some(module) = self.modules.get_mut(&path) {
            module.exports.insert(name.to_string());
        }
        Ok(())
    }

    pub fn module_use(
        &mut self,
        target_path: &str,
        aliases: &HashMap<String, String>,
    ) -> Result<(), String> {
        let Some(current_path) = self.current_module.clone() else {
            return Err(
                "no current module; call Module open: first".to_string()
            );
        };
        self.ensure_module(&current_path);
        self.ensure_module(target_path);

        let target = self.modules.get(target_path).ok_or_else(|| {
            format!("unknown module '{}': not found", target_path)
        })?;

        let mut imports: Vec<(String, ModuleImport)> = Vec::new();
        let mut seen_targets: HashSet<String> = HashSet::new();

        for exported in &target.exports {
            let local_name = aliases
                .get(exported)
                .cloned()
                .unwrap_or_else(|| exported.clone());
            if !seen_targets.insert(local_name.clone()) {
                return Err(format!(
                    "import alias collision: '{}' appears multiple times",
                    local_name
                ));
            }
            imports.push((
                local_name,
                ModuleImport {
                    module_path: target_path.to_string(),
                    export_name: exported.clone(),
                },
            ));
        }

        for from in aliases.keys() {
            if !target.exports.contains(from) {
                return Err(format!(
                    "cannot alias non-exported symbol '{}' from module '{}'",
                    from, target_path
                ));
            }
        }

        let current = self
            .modules
            .get(&current_path)
            .ok_or_else(|| "current module missing".to_string())?;
        for (local_name, import) in &imports {
            if current.bindings.contains_key(local_name) {
                return Err(format!(
                    "import collision in module '{}': '{}' already exists",
                    current_path, local_name
                ));
            }
            if let Some(existing) = current.imports.get(local_name) {
                if existing != import {
                    return Err(format!(
                        "import collision in module '{}': '{}' already exists",
                        current_path, local_name
                    ));
                }
            }
        }

        let current = self
            .modules
            .get_mut(&current_path)
            .ok_or_else(|| "current module missing".to_string())?;
        for (local_name, import) in imports {
            current.imports.insert(local_name, import);
        }
        if !current.uses.iter().any(|u| u == target_path) {
            current.uses.push(target_path.to_string());
        }
        Ok(())
    }

    pub fn module_public_entries(
        &self,
        path: &str,
    ) -> Result<Vec<(String, Value)>, String> {
        let module = self
            .modules
            .get(path)
            .ok_or_else(|| format!("module '{}' not found", path))?;
        let mut out = Vec::new();
        for name in &module.exports {
            if let Some(value) = module.bindings.get(name) {
                out.push((name.clone(), *value));
            }
        }
        Ok(out)
    }
}

/// Trace all Value edges of a heap object for the GC.
///
/// # Safety
///
/// `obj` must point to a valid, live heap object with a valid [`Header`].
pub unsafe fn trace_object(
    obj: *const u8,
    visitor: &mut dyn FnMut(&mut Value),
) {
    let header = &*(obj as *const Header);
    match header.object_type() {
        ObjectType::Slots => {
            let slot_obj = &mut *(obj as *mut SlotObject);
            visitor(&mut slot_obj.map);
            // Read the map to find how many inline values follow
            if slot_obj.map.is_ref() {
                let map: &Map = slot_obj.map.as_ref();
                let count = map.value_count() as usize;
                let values_base = (obj as *mut Value).add(2); // skip header + map
                for i in 0..count {
                    visitor(&mut *values_base.add(i));
                }
            }
        }
        ObjectType::Map => {
            let map = &mut *(obj as *mut Map);
            visitor(&mut map.map);
            visitor(&mut map.code);
            // Visit slot name and value fields
            let slot_count = map.slot_count() as usize;
            let slots = map.slots();
            for i in 0..slot_count {
                let slot_ptr = slots.as_ptr().add(i) as *mut object::Slot;
                visitor(&mut (*slot_ptr).name);
                visitor(&mut (*slot_ptr).value);
            }
        }
        ObjectType::Block => {
            let block = &mut *(obj as *mut Block);
            visitor(&mut block.map);
            visitor(&mut block.env);
            visitor(&mut block.self_value);
        }
        ObjectType::Array => {
            let array = &*(obj as *const Array);
            let count = array.len() as usize;
            // Elements start right after the Array struct (header + length)
            let elems_base =
                (obj as *mut u8).add(size_of::<Array>()) as *mut Value;
            for i in 0..count {
                visitor(&mut *elems_base.add(i));
            }
        }
        ObjectType::Code => {
            let code = &*(obj as *const Code);
            let count = code.constant_count() as usize;
            // Constants start right after the Code struct
            let consts_base =
                (obj as *mut u8).add(size_of::<Code>()) as *mut Value;
            for i in 0..count {
                visitor(&mut *consts_base.add(i));
            }
        }
        ObjectType::Str => {
            let s = &mut *(obj as *mut VMString);
            visitor(&mut s.data);
        }
        ObjectType::Symbol => {
            let s = &mut *(obj as *mut VMSymbol);
            visitor(&mut s.data);
        }
        ObjectType::ByteArray
        | ObjectType::BigNum
        | ObjectType::Alien
        | ObjectType::Float => {
            // No reference fields
        }
        ObjectType::Ratio => {
            let ratio = &mut *(obj as *mut object::Ratio);
            visitor(&mut ratio.numerator);
            visitor(&mut ratio.denominator);
        }
    }
}

/// If `ptr` points to an already-evacuated object (ESCAPED flag is set),
/// return the forwarding pointer stored at `ptr + size_of::<Header>()`;
/// otherwise return `ptr` unchanged.
///
/// Used by [`object_size`] to resolve the map pointer of a [`SlotObject`]
/// whose map may have been evacuated before we compute the slot object's size.
///
/// # Safety
///
/// `ptr` must point to a valid heap object with an initialised [`Header`].
unsafe fn resolve_fwd(ptr: *const u8) -> *const u8 {
    let header = &*(ptr as *const Header);
    if header.has_flag(HeaderFlags::ESCAPED) {
        // The forwarding pointer was written at offset = size_of::<Header>()
        // with a Release fence; it is safe to read here with the Acquire load
        // that observed the ESCAPED flag.
        std::ptr::read(
            ptr.add(std::mem::size_of::<Header>()) as *const *const u8
        )
    } else {
        ptr
    }
}

/// Compute the total byte size of a heap object.
///
/// This is the counterpart of [`trace_object`] used by the evacuation path
/// to know how many bytes to copy. The caller must invoke this function
/// **before** writing a forwarding pointer into the object's first payload
/// word.
///
/// Returns `0` for [`ObjectType::Alien`] as a sentinel meaning "do not
/// evacuate" (Alien objects wrap raw FFI pointers whose ownership semantics
/// are unknown).
///
/// # Safety
///
/// `obj` must point to a valid, live heap object. Its first payload word
/// (`obj + size_of::<Header>()`) must still contain the original field
/// content (not yet overwritten by a forwarding pointer).
pub unsafe fn object_size(obj: *const u8) -> usize {
    let header = &*(obj as *const Header);
    match header.object_type() {
        ObjectType::Slots => {
            // Read the map pointer at offset +size_of::<Header>().
            // The map object may itself have been evacuated already, but only
            // its first field (+8 within the map) is overwritten; value_count
            // sits at a higher offset and is still valid in the old map copy.
            let raw_map = std::ptr::read(
                obj.add(std::mem::size_of::<Header>()) as *const *const u8,
            );
            let map = &*(resolve_fwd(raw_map) as *const Map);
            object::slot_object_allocation_size(map.value_count())
        }
        ObjectType::Map => {
            let map = &*(obj as *const Map);
            map.byte_size()
        }
        ObjectType::Array => {
            let arr = &*(obj as *const Array);
            std::mem::size_of::<Array>()
                + arr.len() as usize * std::mem::size_of::<Value>()
        }
        ObjectType::ByteArray => {
            let ba = &*(obj as *const ByteArray);
            // Round up to 8-byte alignment so the allocator's bump pointer
            // stays aligned.
            (std::mem::size_of::<ByteArray>() + ba.len() as usize + 7) & !7
        }
        ObjectType::Code => {
            let code = &*(obj as *const Code);
            code.byte_size()
        }
        ObjectType::Block => std::mem::size_of::<Block>(),
        ObjectType::Float => std::mem::size_of::<Float>(),
        ObjectType::Ratio => std::mem::size_of::<Ratio>(),
        ObjectType::Str => std::mem::size_of::<VMString>(),
        ObjectType::Symbol => std::mem::size_of::<VMSymbol>(),
        ObjectType::BigNum => {
            let bn = &*(obj as *const BigNum);
            std::mem::size_of::<BigNum>()
                + bn.len() * std::mem::size_of::<u64>()
        }
        // Alien wraps a raw FFI pointer; we do not know its ownership
        // semantics, so we refuse to evacuate it.
        ObjectType::Alien => 0,
    }
}

/// The [`SizeFn`] pointer passed to [`heap::Heap::new`].
pub const OBJECT_SIZE_FN: SizeFn = object_size;
