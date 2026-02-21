pub mod alloc;
pub mod compiler0;
pub mod image;
pub mod interpreter;
pub mod materialize;
pub mod primitives;
pub mod special;
pub mod threading;

use std::collections::{HashMap, HashSet};
use std::ops::Deref;
use std::sync::{
    atomic::{AtomicU64, Ordering},
    Arc, Condvar, Mutex,
};

use crate::threading::PlatformThread;
use heap::{HeapProxy, RootProvider, SizeFn};
use object::{
    Array, BigNum, Block, ByteArray, Code, Float, Header, HeaderFlags, Map,
    ObjectType, Ratio, SlotObject, SpecialObjects, VMString, VMSymbol, Value,
};

pub const USER_MODULE: &str = "User";
pub const CORE_MODULE: &str = "Core";

/// The VM owns a heap proxy and the bootstrapped special objects.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModuleImport {
    pub module_path: String,
    pub export_name: String,
}

#[derive(Debug, Default, Clone)]
pub struct ModuleState {
    pub bindings: HashMap<String, Value>,
    pub imports: HashMap<String, ModuleImport>,
    pub uses: Vec<String>,
    pub exports: HashSet<String>,
}

pub struct SharedVMData {
    pub heap: heap::Heap,
    pub special: SpecialObjects,
    /// Registered primitive descriptors.
    pub primitives: Vec<primitives::PrimitiveDesc>,
    /// Shared map for all assoc objects (0 named slots, value_count=1).
    pub assoc_map: Value,
    /// The global dictionary object (SlotObject whose map has one CONSTANT
    /// slot per global).
    pub dictionary: Value,
    /// Interned symbols: Rust string -> heap symbol Value.
    pub intern_table: Mutex<HashMap<String, Value>>,
    /// Runtime module registry.
    pub modules: Mutex<HashMap<String, ModuleState>>,
    /// Next platform-thread handle id.
    pub next_thread_id: AtomicU64,
    /// Join handles for spawned platform threads.
    pub platform_threads: Mutex<HashMap<u64, PlatformThreadEntry>>,
    /// Object lock records keyed by raw object pointer bits.
    pub lock_records: Mutex<HashMap<u64, Arc<LockRecord>>>,
}

pub struct VMProxy {
    pub heap_proxy: HeapProxy,
    pub special: SpecialObjects,
    pub assoc_map: Value,
    pub dictionary: Value,
    /// Currently open module path. `None` means legacy global dictionary mode.
    pub current_module: Option<String>,
    /// Optional global assoc name to trace load/store.
    #[cfg(debug_assertions)]
    pub trace_assoc_name: Option<String>,
    /// Optional message selector to trace sends.
    #[cfg(debug_assertions)]
    pub trace_send_name: Option<String>,
    pub shared: Arc<SharedVMData>,
}

pub type VM = VMProxy;

pub struct PlatformThreadEntry {
    pub handle: PlatformThread<Result<Value, String>>,
    pub root_code: Value,
}

#[derive(Debug)]
pub struct LockRecord {
    pub monitor: Mutex<Option<Arc<Monitor>>>,
}

#[derive(Debug)]
pub struct Monitor {
    pub state: Mutex<MonitorState>,
    pub cvar: Condvar,
}

#[derive(Debug, Default)]
pub struct MonitorState {
    pub owner: Option<u64>,
    pub recursion: u32,
}

impl RootProvider for VMProxy {
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
        {
            let mut modules =
                self.shared.modules.lock().expect("modules poisoned");
            for module in modules.values_mut() {
                for value in module.bindings.values_mut() {
                    visitor(value);
                }
            }
        }
        {
            let mut threads = self
                .shared
                .platform_threads
                .lock()
                .expect("platform threads poisoned");
            for thread in threads.values_mut() {
                visitor(&mut thread.root_code);
            }
        }
        {
            let mut table = self
                .shared
                .intern_table
                .lock()
                .expect("intern table poisoned");
            for v in table.values_mut() {
                visitor(v);
            }
        }
    }
}

impl VMProxy {
    pub fn new(shared: Arc<SharedVMData>) -> Self {
        let heap_proxy = HeapProxy::new(shared.heap.clone());
        Self {
            heap_proxy,
            special: shared.special,
            assoc_map: shared.assoc_map,
            dictionary: shared.dictionary,
            current_module: None,
            #[cfg(debug_assertions)]
            trace_assoc_name: None,
            #[cfg(debug_assertions)]
            trace_send_name: None,
            shared,
        }
    }

    pub fn spawn_proxy(&self) -> Self {
        Self::new(self.shared.clone())
    }

    pub fn next_thread_id(&self) -> u64 {
        self.shared.next_thread_id.fetch_add(1, Ordering::Relaxed)
    }

    pub fn with_intern_table<R>(
        &self,
        f: impl FnOnce(&mut HashMap<String, Value>) -> R,
    ) -> R {
        let mut table = self
            .shared
            .intern_table
            .lock()
            .expect("intern table poisoned");
        f(&mut table)
    }

    pub fn with_modules<R>(
        &self,
        f: impl FnOnce(&mut HashMap<String, ModuleState>) -> R,
    ) -> R {
        let mut modules = self.shared.modules.lock().expect("modules poisoned");
        f(&mut modules)
    }

    pub fn with_platform_threads<R>(
        &self,
        f: impl FnOnce(&mut HashMap<u64, PlatformThreadEntry>) -> R,
    ) -> R {
        let mut threads = self
            .shared
            .platform_threads
            .lock()
            .expect("platform threads poisoned");
        f(&mut threads)
    }
}

impl Deref for VMProxy {
    type Target = SharedVMData;

    fn deref(&self) -> &Self::Target {
        &self.shared
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

        let (has_binding, import) = self.with_modules(|modules| {
            let module = modules.get(module_path)?;
            Some((
                module.bindings.contains_key(name),
                module.imports.get(name).cloned(),
            ))
        })?;
        if has_binding {
            return Some((module_path.to_string(), name.to_string()));
        }

        let import = import?;
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

        let import = self.with_modules(|modules| {
            let module = modules.get(module_path)?;
            module.imports.get(name).cloned()
        });
        if let Some(import) = import {
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
        self.with_modules(|modules| {
            modules
                .get(&owner_path)
                .and_then(|m| m.bindings.get(&owner_name))
                .copied()
        })
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

        self.with_modules(|modules| {
            if let Some(module) = modules.get_mut(&owner_path) {
                module.bindings.insert(owner_name, value);
                true
            } else {
                false
            }
        })
    }

    pub fn module_owner_of_value(&self, value: Value) -> Option<String> {
        if !value.is_ref() {
            return None;
        }

        let mut result = None;
        self.with_modules(|modules| {
            for (path, module) in modules.iter() {
                if module.bindings.values().any(|v| v.raw() == value.raw()) {
                    result = Some(path.clone());
                    break;
                }
            }
        });

        result
    }

    pub fn ensure_module(&mut self, path: &str) {
        self.with_modules(|modules| {
            modules.entry(path.to_string()).or_default();
        });
    }

    pub fn seed_user_module_from_dictionary(&mut self) {
        self.ensure_module(USER_MODULE);
        self.ensure_module(CORE_MODULE);
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

        self.with_modules(|modules| {
            if let Some(user) = modules.get_mut(USER_MODULE) {
                for (name, value) in &entries {
                    user.bindings.insert(name.clone(), *value);
                    user.exports.insert(name.clone());
                }
            }

            if let Some(core) = modules.get_mut(CORE_MODULE) {
                for (name, value) in &entries {
                    core.bindings.insert(name.clone(), *value);
                    core.exports.insert(name.clone());
                }
            }
        });
    }

    pub fn open_module(&mut self, path: &str) {
        self.ensure_module(path);
        self.current_module = Some(path.to_string());
        if path != CORE_MODULE {
            let _ = self.module_use(CORE_MODULE, &HashMap::new());
        }
    }

    pub fn current_module_state(&self) -> Option<ModuleState> {
        let path = self.current_module.as_ref()?;
        self.with_modules(|modules| modules.get(path).cloned())
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
        self.with_modules(|modules| {
            if let Some(module) = modules.get_mut(&path) {
                module.exports.insert(name.to_string());
            }
        });
        Ok(())
    }

    pub fn module_use(
        &mut self,
        target_path: &str,
        aliases: &HashMap<String, String>,
    ) -> Result<(), String> {
        self.module_use_filtered(target_path, aliases, None)
    }

    pub fn module_use_only(
        &mut self,
        target_path: &str,
        names: &HashSet<String>,
    ) -> Result<(), String> {
        self.module_use_filtered(target_path, &HashMap::new(), Some(names))
    }

    fn module_use_filtered(
        &mut self,
        target_path: &str,
        aliases: &HashMap<String, String>,
        only_names: Option<&HashSet<String>>,
    ) -> Result<(), String> {
        let Some(current_path) = self.current_module.clone() else {
            return Err(
                "no current module; call Module open: first".to_string()
            );
        };
        self.with_modules(|modules| {
            modules.entry(current_path.clone()).or_default();
            modules.entry(target_path.to_string()).or_default();

            let target = modules.get(target_path).ok_or_else(|| {
                format!("unknown module '{}': not found", target_path)
            })?;

            let mut imports: Vec<(String, ModuleImport)> = Vec::new();
            let mut seen_targets: HashSet<String> = HashSet::new();

            for exported in &target.exports {
                if let Some(only) = only_names {
                    if !only.contains(exported) {
                        continue;
                    }
                }
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

            if let Some(only) = only_names {
                for name in only {
                    if !target.exports.contains(name) {
                        return Err(format!(
                            "cannot import non-exported symbol '{}' from module '{}'",
                            name, target_path
                        ));
                    }
                }
            }

            let current = modules
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

            let current = modules
                .get_mut(&current_path)
                .ok_or_else(|| "current module missing".to_string())?;
            for (local_name, import) in imports {
                current.imports.insert(local_name, import);
            }
            if !current.uses.iter().any(|u| u == target_path) {
                current.uses.push(target_path.to_string());
            }
            Ok(())
        })
    }

    pub fn module_public_entries(
        &self,
        path: &str,
    ) -> Result<Vec<(String, Value)>, String> {
        self.with_modules(|modules| {
            let module = modules
                .get(path)
                .ok_or_else(|| format!("module '{}' not found", path))?;
            let mut out = Vec::new();
            for name in &module.exports {
                if let Some(value) = module.bindings.get(name) {
                    out.push((name.clone(), *value));
                }
            }
            Ok(out)
        })
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
            let code_ptr = obj as *mut Code;
            visitor(&mut (*code_ptr).feedback);
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
    let obj_type = header.object_type();
    match obj_type {
        ObjectType::Slots => {
            // Read the map pointer at offset +size_of::<Header>().
            // The map object may itself have been evacuated already, but only
            // its first field (+8 within the map) is overwritten; value_count
            // sits at a higher offset and is still valid in the old map copy.
            let raw_map_val = std::ptr::read(
                obj.add(std::mem::size_of::<Header>()) as *const Value,
            );
            if !raw_map_val.is_ref() {
                return 0;
            }
            let raw_map = raw_map_val.ref_bits() as *const u8;
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
