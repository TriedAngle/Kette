pub mod alloc;
pub mod compiler0;
pub mod interpreter;
pub mod materialize;
pub mod primitives;
pub mod special;

use std::collections::HashMap;

use heap::{HeapProxy, RootProvider, SizeFn};
use libffi::middle::Cif;
use object::{
    Array, BigNum, Block, ByteArray, Code, Float, Header, HeaderFlags, Map,
    ObjectType, Ratio, SlotObject, SpecialObjects, VMString, Value,
};

/// The VM owns a heap proxy and the bootstrapped special objects.
pub struct VM {
    pub heap_proxy: HeapProxy,
    pub special: SpecialObjects,
    /// Interned symbols: Rust string → heap VMString Value.
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
        visitor(&mut self.special.ratio_traits);
        visitor(&mut self.special.fixnum_traits);
        visitor(&mut self.special.code_traits);
        visitor(&mut self.special.float_traits);
        visitor(&mut self.special.mirror);
        visitor(&mut self.assoc_map);
        visitor(&mut self.dictionary);
        for v in self.intern_table.values_mut() {
            visitor(v);
        }
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
