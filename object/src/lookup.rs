use crate::header::ObjectType;
use crate::map::Map;
use crate::objects::{Block, SlotObject};
use crate::slot::Slot;
use crate::special::SpecialObjects;
use crate::Value;

/// Stack-allocated linked list for cycle detection.
///
/// Each node lives on a recursive call's stack frame and points to the
/// caller's node. Because every node outlives its callees, the raw pointer
/// chain is always valid for the duration of a lookup.
pub struct VisitedLink {
    value: Value,
    prev: *const VisitedLink,
}

impl VisitedLink {
    #[inline]
    fn contains(mut link: *const Self, target: Value) -> bool {
        while !link.is_null() {
            // SAFETY: all nodes are stack-allocated in the recursion chain
            // and remain valid for the duration of the lookup.
            let node = unsafe { &*link };
            if node.value.raw() == target.raw() {
                return true;
            }
            link = node.prev;
        }
        false
    }
}

/// The result of a slot lookup.
#[derive(Debug, Clone, Copy)]
pub enum LookupResult {
    /// Name was not found.
    None,
    /// Name was found.
    Found {
        /// The object that owns the slot (may differ from the receiver if
        /// the slot was found via a parent link).
        holder: Value,
        /// Copy of the matching slot descriptor.
        slot: Slot,
        /// Index of the slot within its map.
        slot_index: u32,
        /// `true` if the lookup traversed at least one assignable parent
        /// slot. When set, an inline cache should not cache this result
        /// because the parent link can change at runtime.
        traversed_assignable_parent: bool,
    },
}

/// Look up `name` on `receiver`.
///
/// Dispatches based on the receiver's object type: objects with a map
/// (Slots, Block) search their map's slot array and walk parent links;
/// primitive types without a map (Array, VMString, …) delegate to the
/// corresponding traits object in `specials`.
///
/// # Safety
///
/// - `receiver` must be a valid tagged reference (or fixnum).
/// - All objects reachable through maps and parent links must be live.
/// - `specials` must contain valid tagged references.
#[inline]
pub unsafe fn lookup(
    receiver: Value,
    name: Value,
    specials: &SpecialObjects,
) -> LookupResult {
    lookup_value(receiver, name, specials, core::ptr::null())
}

unsafe fn lookup_value(
    receiver: Value,
    name: Value,
    specials: &SpecialObjects,
    visited: *const VisitedLink,
) -> LookupResult {
    if receiver.is_fixnum() {
        return lookup_value(specials.fixnum_traits, name, specials, visited);
    }

    debug_assert!(receiver.is_ref());

    let header: &crate::Header = receiver.as_ref();
    match header.object_type() {
        ObjectType::Slots => {
            let obj: &SlotObject = receiver.as_ref();
            lookup_in_slot_object(obj, receiver, name, specials, visited)
        }
        ObjectType::Block => {
            // Block has the same header+map prefix as SlotObject.
            let obj: &Block = receiver.as_ref();
            let as_slot_obj = &*(obj as *const Block as *const SlotObject);
            lookup_in_slot_object(
                as_slot_obj,
                receiver,
                name,
                specials,
                visited,
            )
        }
        ObjectType::Map => {
            let map: &Map = receiver.as_ref();
            lookup_in_map(map, receiver, name, specials, visited)
        }
        ObjectType::Array => {
            lookup_value(specials.array_traits, name, specials, visited)
        }
        ObjectType::ByteArray => {
            lookup_value(specials.bytearray_traits, name, specials, visited)
        }
        ObjectType::Str => {
            lookup_value(specials.string_traits, name, specials, visited)
        }
        ObjectType::BigNum => {
            lookup_value(specials.bignum_traits, name, specials, visited)
        }
        ObjectType::Alien => {
            lookup_value(specials.alien_traits, name, specials, visited)
        }
        ObjectType::Ratio => {
            lookup_value(specials.ratio_traits, name, specials, visited)
        }
        ObjectType::Code => {
            lookup_value(specials.code_traits, name, specials, visited)
        }
        ObjectType::Float => {
            lookup_value(specials.float_traits, name, specials, visited)
        }
    }
}

/// Search a SlotObject's map for `name`, then walk parent links.
unsafe fn lookup_in_slot_object(
    obj: &SlotObject,
    obj_value: Value,
    name: Value,
    specials: &SpecialObjects,
    visited: *const VisitedLink,
) -> LookupResult {
    // Cycle check.
    if VisitedLink::contains(visited, obj_value) {
        return LookupResult::None;
    }

    let map: &Map = obj.map.as_ref();
    let slots = map.slots();

    // Local scan — look for a slot whose name matches.
    for (i, slot) in slots.iter().enumerate() {
        if slot.name.raw() != name.raw() {
            continue;
        }

        // Resolve the value for assignable slots.
        let resolved_slot = if slot.is_assignable() {
            let offset = slot.value.to_i64() as u32;
            let val = obj.read_value(offset);
            Slot::new(slot.flags(), slot.name, val)
        } else {
            *slot
        };

        return LookupResult::Found {
            holder: obj_value,
            slot: resolved_slot,
            slot_index: i as u32,
            traversed_assignable_parent: false,
        };
    }

    // Parent walk.
    let link = VisitedLink {
        value: obj_value,
        prev: visited,
    };

    for slot in slots.iter() {
        if !slot.is_parent() {
            continue;
        }

        let parent = if slot.is_assignable() {
            let offset = slot.value.to_i64() as u32;
            obj.read_value(offset)
        } else {
            // CONSTANT | PARENT — value is stored directly in the slot.
            slot.value
        };

        let is_assignable_parent = slot.is_assignable();

        match lookup_value(parent, name, specials, &link) {
            LookupResult::None => continue,
            LookupResult::Found {
                holder,
                slot: found_slot,
                slot_index,
                traversed_assignable_parent,
            } => {
                return LookupResult::Found {
                    holder,
                    slot: found_slot,
                    slot_index,
                    traversed_assignable_parent: traversed_assignable_parent
                        || is_assignable_parent,
                };
            }
        }
    }

    LookupResult::None
}

/// Search a Map object itself (meta-level lookup on maps).
///
/// A Map has its own `map` field (pointing to `map_map`), its own slots,
/// and potentially parent links — same algorithm as SlotObject but the
/// "object" is the Map itself.
unsafe fn lookup_in_map(
    map: &Map,
    map_value: Value,
    name: Value,
    specials: &SpecialObjects,
    visited: *const VisitedLink,
) -> LookupResult {
    if VisitedLink::contains(visited, map_value) {
        return LookupResult::None;
    }

    // A Map's own slots describe the map object's properties.
    // For meta-level lookup we search the meta-map (map.map).
    let meta_map: &Map = map.map.as_ref();
    let slots = meta_map.slots();

    for (i, slot) in slots.iter().enumerate() {
        if slot.name.raw() != name.raw() {
            continue;
        }

        let resolved_slot = if slot.is_assignable() {
            // Read from the map object body — cast to raw bytes.
            let ptr = (map as *const Map as *const u8)
                .add(slot.value.to_i64() as usize);
            let val = *(ptr as *const Value);
            Slot::new(slot.flags(), slot.name, val)
        } else {
            *slot
        };

        return LookupResult::Found {
            holder: map_value,
            slot: resolved_slot,
            slot_index: i as u32,
            traversed_assignable_parent: false,
        };
    }

    // Parent walk on the meta-map's slots.
    let link = VisitedLink {
        value: map_value,
        prev: visited,
    };

    for slot in slots.iter() {
        if !slot.is_parent() {
            continue;
        }

        let parent = if slot.is_assignable() {
            let ptr = (map as *const Map as *const u8)
                .add(slot.value.to_i64() as usize);
            *(ptr as *const Value)
        } else {
            slot.value
        };

        let is_assignable_parent = slot.is_assignable();

        match lookup_value(parent, name, specials, &link) {
            LookupResult::None => continue,
            LookupResult::Found {
                holder,
                slot: found_slot,
                slot_index,
                traversed_assignable_parent,
            } => {
                return LookupResult::Found {
                    holder,
                    slot: found_slot,
                    slot_index,
                    traversed_assignable_parent: traversed_assignable_parent
                        || is_assignable_parent,
                };
            }
        }
    }

    LookupResult::None
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        init_map, map_allocation_size, slot_object_allocation_size, Header,
        Map, SlotFlags, SlotObject,
    };

    /// Dummy specials where all trait objects point to nil (fixnum 0).
    fn dummy_specials() -> SpecialObjects {
        let nil = Value::from_i64(0);
        SpecialObjects {
            nil,
            true_obj: nil,
            false_obj: nil,
            map_map: nil,
            array_traits: nil,
            bytearray_traits: nil,
            bignum_traits: nil,
            alien_traits: nil,
            string_traits: nil,
            ratio_traits: nil,
            fixnum_traits: nil,
            code_traits: nil,
            float_traits: nil,
        }
    }

    /// Helper: allocate a map in a Vec with the given slots.
    /// Returns (buffer, Value pointing to the Map).
    fn alloc_map(map_map: Value, slots: &[Slot]) -> (Vec<u8>, Value) {
        let count = slots.len() as u32;
        let size = map_allocation_size(count);
        let mut buf = vec![0u8; size];
        let ptr = buf.as_mut_ptr() as *mut Map;
        // Count value slots (assignable slots).
        let value_count =
            slots.iter().filter(|s| s.is_assignable()).count() as u32;
        unsafe {
            init_map(ptr, map_map, Value::from_i64(0), count, value_count);
            let slot_dst = ptr.add(1) as *mut Slot;
            for (i, slot) in slots.iter().enumerate() {
                slot_dst.add(i).write(*slot);
            }
        }
        let val = Value::from_ptr(buf.as_ptr());
        (buf, val)
    }

    /// Helper: allocate a SlotObject with the given map and inline values.
    fn alloc_slot_object(map: Value, values: &[Value]) -> (Vec<u8>, Value) {
        let size = slot_object_allocation_size(values.len() as u32);
        let mut buf = vec![0u8; size];
        let ptr = buf.as_mut_ptr() as *mut SlotObject;
        unsafe {
            ptr.write(SlotObject {
                header: Header::new(ObjectType::Slots),
                map,
            });
            let val_dst = (ptr as *mut u8)
                .add(SlotObject::VALUES_OFFSET as usize)
                as *mut Value;
            for (i, v) in values.iter().enumerate() {
                val_dst.add(i).write(*v);
            }
        }
        let val = Value::from_ptr(buf.as_ptr());
        (buf, val)
    }

    // ── Tests ──────────────────────────────────────────────────────────

    #[test]
    fn lookup_constant_slot() {
        let specials = dummy_specials();
        let name = Value::from_i64(100);
        let slot_value = Value::from_i64(42);

        let slot = Slot::new(SlotFlags::CONSTANT, name, slot_value);
        let (_map_buf, map_val) = alloc_map(specials.nil, &[slot]);
        let (_obj_buf, obj_val) = alloc_slot_object(map_val, &[]);

        unsafe {
            match lookup(obj_val, name, &specials) {
                LookupResult::Found {
                    holder,
                    slot,
                    slot_index,
                    traversed_assignable_parent,
                } => {
                    assert_eq!(holder.raw(), obj_val.raw());
                    assert_eq!(slot.value.raw(), slot_value.raw());
                    assert_eq!(slot_index, 0);
                    assert!(!traversed_assignable_parent);
                }
                LookupResult::None => panic!("expected Found"),
            }
        }
    }

    #[test]
    fn lookup_assignable_slot() {
        let specials = dummy_specials();
        let name = Value::from_i64(200);
        let stored_value = Value::from_i64(99);

        // Assignable slot: value field stores the byte offset.
        let offset = SlotObject::VALUES_OFFSET;
        let slot = Slot::new(
            SlotFlags::ASSIGNABLE,
            name,
            Value::from_i64(offset as i64),
        );
        let (_map_buf, map_val) = alloc_map(specials.nil, &[slot]);
        // The first inline value at VALUES_OFFSET.
        let (_obj_buf, obj_val) = alloc_slot_object(map_val, &[stored_value]);

        unsafe {
            match lookup(obj_val, name, &specials) {
                LookupResult::Found { slot, .. } => {
                    // The resolved slot value should be the stored value, not the offset.
                    assert_eq!(slot.value.raw(), stored_value.raw());
                }
                LookupResult::None => panic!("expected Found"),
            }
        }
    }

    #[test]
    fn lookup_parent_delegation() {
        let specials = dummy_specials();
        let child_name = Value::from_i64(300);
        let parent_name = Value::from_i64(400);
        let parent_value = Value::from_i64(77);

        // Parent object has a constant slot.
        let parent_slot =
            Slot::new(SlotFlags::CONSTANT, parent_name, parent_value);
        let (_parent_map_buf, parent_map_val) =
            alloc_map(specials.nil, &[parent_slot]);
        let (_parent_buf, parent_val) = alloc_slot_object(parent_map_val, &[]);

        // Child object has a CONSTANT | PARENT slot pointing to parent.
        let parent_link = Slot::new(
            SlotFlags::CONSTANT.with(SlotFlags::PARENT),
            child_name,
            parent_val,
        );
        let (_child_map_buf, child_map_val) =
            alloc_map(specials.nil, &[parent_link]);
        let (_child_buf, child_val) = alloc_slot_object(child_map_val, &[]);

        unsafe {
            match lookup(child_val, parent_name, &specials) {
                LookupResult::Found {
                    holder,
                    slot,
                    traversed_assignable_parent,
                    ..
                } => {
                    // Found on the parent, not the child.
                    assert_eq!(holder.raw(), parent_val.raw());
                    assert_eq!(slot.value.raw(), parent_value.raw());
                    assert!(!traversed_assignable_parent);
                }
                LookupResult::None => panic!("expected Found"),
            }
        }
    }

    #[test]
    fn lookup_cycle_detection() {
        let specials = dummy_specials();
        let name = Value::from_i64(500);

        // Create two objects that are each other's parents.
        // We need to set up the parent links after allocation since they
        // reference each other.

        // Allocate map A: CONSTANT | PARENT slot (value will be patched).
        let slot_a = Slot::new(
            SlotFlags::CONSTANT.with(SlotFlags::PARENT),
            Value::from_i64(1), // parent link name
            Value::from_i64(0), // placeholder
        );
        let (mut map_a_buf, map_a_val) = alloc_map(specials.nil, &[slot_a]);

        // Allocate map B: CONSTANT | PARENT slot (value will be patched).
        let slot_b = Slot::new(
            SlotFlags::CONSTANT.with(SlotFlags::PARENT),
            Value::from_i64(2), // parent link name
            Value::from_i64(0), // placeholder
        );
        let (mut map_b_buf, map_b_val) = alloc_map(specials.nil, &[slot_b]);

        let (_obj_a_buf, obj_a_val) = alloc_slot_object(map_a_val, &[]);
        let (_obj_b_buf, obj_b_val) = alloc_slot_object(map_b_val, &[]);

        // Patch: map A's parent slot → obj B.
        unsafe {
            let map_a = &mut *(map_a_buf.as_mut_ptr() as *mut Map);
            let slot_ptr = (map_a as *mut Map).add(1) as *mut Slot;
            (*slot_ptr).value = obj_b_val;
        }
        // Patch: map B's parent slot → obj A.
        unsafe {
            let map_b = &mut *(map_b_buf.as_mut_ptr() as *mut Map);
            let slot_ptr = (map_b as *mut Map).add(1) as *mut Slot;
            (*slot_ptr).value = obj_a_val;
        }

        // Lookup should terminate without hanging.
        unsafe {
            match lookup(obj_a_val, name, &specials) {
                LookupResult::None => {} // Expected — name doesn't exist.
                LookupResult::Found { .. } => panic!("expected None"),
            }
        }
    }

    #[test]
    fn lookup_primitive_forwards() {
        // Array traits object has a slot we can find.
        let name = Value::from_i64(600);
        let val = Value::from_i64(88);

        let slot = Slot::new(SlotFlags::CONSTANT, name, val);
        let (_traits_map_buf, traits_map_val) =
            alloc_map(Value::from_i64(0), &[slot]);
        let (_traits_buf, traits_val) = alloc_slot_object(traits_map_val, &[]);

        let mut specials = dummy_specials();
        specials.array_traits = traits_val;

        // Create a minimal Array object.
        let mut arr_buf = vec![0u8; 16];
        let arr_ptr = arr_buf.as_mut_ptr() as *mut crate::Array;
        unsafe {
            crate::init_array(arr_ptr, 0);
        }
        let arr_val = Value::from_ptr(arr_buf.as_ptr());

        unsafe {
            match lookup(arr_val, name, &specials) {
                LookupResult::Found { slot, .. } => {
                    assert_eq!(slot.value.raw(), val.raw());
                }
                LookupResult::None => panic!("expected Found"),
            }
        }
    }

    #[test]
    fn lookup_miss() {
        let specials = dummy_specials();
        let name = Value::from_i64(700);

        let slot = Slot::new(
            SlotFlags::CONSTANT,
            Value::from_i64(999),
            Value::from_i64(1),
        );
        let (_map_buf, map_val) = alloc_map(specials.nil, &[slot]);
        let (_obj_buf, obj_val) = alloc_slot_object(map_val, &[]);

        unsafe {
            match lookup(obj_val, name, &specials) {
                LookupResult::None => {} // Expected.
                LookupResult::Found { .. } => panic!("expected None"),
            }
        }
    }

    #[test]
    fn lookup_dynamic_parent() {
        let specials = dummy_specials();
        let target_name = Value::from_i64(800);
        let target_value = Value::from_i64(55);

        // Parent object has the slot we're looking for.
        let parent_slot =
            Slot::new(SlotFlags::CONSTANT, target_name, target_value);
        let (_parent_map_buf, parent_map_val) =
            alloc_map(specials.nil, &[parent_slot]);
        let (_parent_buf, parent_val) = alloc_slot_object(parent_map_val, &[]);

        // Child has an ASSIGNABLE | PARENT slot.
        // The slot value stores the byte offset where the parent ref lives.
        let offset = SlotObject::VALUES_OFFSET;
        let parent_link = Slot::new(
            SlotFlags::ASSIGNABLE.with(SlotFlags::PARENT),
            Value::from_i64(1), // parent link name
            Value::from_i64(offset as i64),
        );
        let (_child_map_buf, child_map_val) =
            alloc_map(specials.nil, &[parent_link]);
        // Inline value 0 = the parent reference.
        let (_child_buf, child_val) =
            alloc_slot_object(child_map_val, &[parent_val]);

        unsafe {
            match lookup(child_val, target_name, &specials) {
                LookupResult::Found {
                    holder,
                    slot,
                    traversed_assignable_parent,
                    ..
                } => {
                    assert_eq!(holder.raw(), parent_val.raw());
                    assert_eq!(slot.value.raw(), target_value.raw());
                    assert!(traversed_assignable_parent);
                }
                LookupResult::None => panic!("expected Found"),
            }
        }
    }

    #[test]
    fn lookup_fixnum_forwards() {
        let name = Value::from_i64(900);
        let val = Value::from_i64(33);

        let slot = Slot::new(SlotFlags::CONSTANT, name, val);
        let (_traits_map_buf, traits_map_val) =
            alloc_map(Value::from_i64(0), &[slot]);
        let (_traits_buf, traits_val) = alloc_slot_object(traits_map_val, &[]);

        let mut specials = dummy_specials();
        specials.fixnum_traits = traits_val;

        let fixnum = Value::from_i64(42);

        unsafe {
            match lookup(fixnum, name, &specials) {
                LookupResult::Found { slot, .. } => {
                    assert_eq!(slot.value.raw(), val.raw());
                }
                LookupResult::None => panic!("expected Found"),
            }
        }
    }

    #[test]
    fn lookup_code_forwards() {
        let name = Value::from_i64(1000);
        let val = Value::from_i64(77);

        let slot = Slot::new(SlotFlags::CONSTANT, name, val);
        let (_traits_map_buf, traits_map_val) =
            alloc_map(Value::from_i64(0), &[slot]);
        let (_traits_buf, traits_val) = alloc_slot_object(traits_map_val, &[]);

        let mut specials = dummy_specials();
        specials.code_traits = traits_val;

        // Create a minimal Code object.
        let mut code_buf = vec![0u8; size_of::<crate::Code>()];
        let code_ptr = code_buf.as_mut_ptr() as *mut crate::Code;
        unsafe {
            crate::init_code(code_ptr, 0, 0, 0, 0, 0);
        }
        let code_val = Value::from_ptr(code_buf.as_ptr());

        unsafe {
            match lookup(code_val, name, &specials) {
                LookupResult::Found { slot, .. } => {
                    assert_eq!(slot.value.raw(), val.raw());
                }
                LookupResult::None => panic!("expected Found"),
            }
        }
    }
}
