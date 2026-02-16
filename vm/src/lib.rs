pub mod alloc;
pub mod compiler0;
pub mod interpreter;
pub mod materialize;
pub mod primitives;
pub mod special;

use std::collections::HashMap;

use heap::{HeapProxy, RootProvider};
use object::{
    Array, Block, Code, Header, Map, ObjectType, SlotObject, SpecialObjects,
    VMString, Value,
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
    /// The global dictionary object (SlotObject whose map has one CONSTANT
    /// slot per global).
    pub dictionary: Value,
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
