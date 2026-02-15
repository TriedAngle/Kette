use std::collections::HashMap;

use object::{Value, SpecialObjects};
use heap::{Heap, HeapSettings, RootProvider};

use crate::alloc::{alloc_map, alloc_slot_object};
use crate::{VM, trace_object};

/// Temporary root provider used during bootstrap.
struct BootstrapRoots {
    roots: Vec<Value>,
}

impl BootstrapRoots {
    fn new() -> Self {
        Self { roots: Vec::with_capacity(16) }
    }

    fn push(&mut self, value: Value) {
        self.roots.push(value);
    }
}

impl RootProvider for BootstrapRoots {
    fn visit_roots(&mut self, visitor: &mut dyn FnMut(&mut Value)) {
        for root in &mut self.roots {
            visitor(root);
        }
    }
}

/// The nil value used as a placeholder before real nil is allocated.
const NIL_PLACEHOLDER: Value = Value::from_raw(0);

/// Bootstrap the VM by allocating all special objects.
///
/// Creates the heap, allocates `map_map` (self-referential), `nil`, `true`,
/// `false`, and all trait maps for primitive types, then returns a fully
/// initialized [`VM`].
pub fn bootstrap(settings: HeapSettings) -> VM {
    let heap = Heap::new(settings, trace_object);
    let mut proxy = heap.proxy();
    let mut roots = BootstrapRoots::new();

    unsafe {
        // 1. map_map — 0-slot Map, temporarily nil map ptr, then patch self-referential
        let map_map_val = alloc_map(
            &mut proxy, &mut roots,
            NIL_PLACEHOLDER, NIL_PLACEHOLDER, &[], 0,
        ).value();
        (*(map_map_val.ref_bits() as *mut object::Map)).map = map_map_val;
        roots.push(map_map_val);

        // 2. nil_map + nil
        let nil_map_val = alloc_map(
            &mut proxy, &mut roots,
            map_map_val, NIL_PLACEHOLDER, &[], 0,
        ).value();
        roots.push(nil_map_val);

        let nil_val = alloc_slot_object(
            &mut proxy, &mut roots, nil_map_val, &[],
        ).value();
        roots.push(nil_val);

        // 3. true_map + true_obj
        let true_map_val = alloc_map(
            &mut proxy, &mut roots,
            map_map_val, NIL_PLACEHOLDER, &[], 0,
        ).value();
        roots.push(true_map_val);

        let true_val = alloc_slot_object(
            &mut proxy, &mut roots, true_map_val, &[],
        ).value();
        roots.push(true_val);

        // 4. false_map + false_obj
        let false_map_val = alloc_map(
            &mut proxy, &mut roots,
            map_map_val, NIL_PLACEHOLDER, &[], 0,
        ).value();
        roots.push(false_map_val);

        let false_val = alloc_slot_object(
            &mut proxy, &mut roots, false_map_val, &[],
        ).value();
        roots.push(false_val);

        // 5. Trait maps for primitive types
        let array_traits_val = alloc_map(
            &mut proxy, &mut roots,
            map_map_val, NIL_PLACEHOLDER, &[], 0,
        ).value();
        roots.push(array_traits_val);

        let bytearray_traits_val = alloc_map(
            &mut proxy, &mut roots,
            map_map_val, NIL_PLACEHOLDER, &[], 0,
        ).value();
        roots.push(bytearray_traits_val);

        let bignum_traits_val = alloc_map(
            &mut proxy, &mut roots,
            map_map_val, NIL_PLACEHOLDER, &[], 0,
        ).value();
        roots.push(bignum_traits_val);

        let alien_traits_val = alloc_map(
            &mut proxy, &mut roots,
            map_map_val, NIL_PLACEHOLDER, &[], 0,
        ).value();
        roots.push(alien_traits_val);

        let string_traits_val = alloc_map(
            &mut proxy, &mut roots,
            map_map_val, NIL_PLACEHOLDER, &[], 0,
        ).value();
        roots.push(string_traits_val);

        let ratio_traits_val = alloc_map(
            &mut proxy, &mut roots,
            map_map_val, NIL_PLACEHOLDER, &[], 0,
        ).value();
        roots.push(ratio_traits_val);

        let fixnum_traits_val = alloc_map(
            &mut proxy, &mut roots,
            map_map_val, NIL_PLACEHOLDER, &[], 0,
        ).value();
        roots.push(fixnum_traits_val);

        let code_traits_val = alloc_map(
            &mut proxy, &mut roots,
            map_map_val, NIL_PLACEHOLDER, &[], 0,
        ).value();
        roots.push(code_traits_val);

        let float_traits_val = alloc_map(
            &mut proxy, &mut roots,
            map_map_val, NIL_PLACEHOLDER, &[], 0,
        ).value();
        roots.push(float_traits_val);

        // 6. assoc_map: 0 named slots, value_count=1 (one inline value per assoc)
        let assoc_map_val = alloc_map(
            &mut proxy, &mut roots,
            map_map_val, NIL_PLACEHOLDER, &[], 1,
        ).value();
        roots.push(assoc_map_val);

        // 7. dictionary_map + dictionary: empty SlotObject with 0-slot map
        let dictionary_map_val = alloc_map(
            &mut proxy, &mut roots,
            map_map_val, NIL_PLACEHOLDER, &[], 0,
        ).value();
        roots.push(dictionary_map_val);

        let dictionary_val = alloc_slot_object(
            &mut proxy, &mut roots, dictionary_map_val, &[],
        ).value();
        roots.push(dictionary_val);

        // 8. Fixup: patch NIL_PLACEHOLDER → real nil in every map's `code` field
        for &map_val in &[
            map_map_val, nil_map_val, true_map_val, false_map_val,
            array_traits_val, bytearray_traits_val, bignum_traits_val,
            alien_traits_val, string_traits_val, ratio_traits_val,
            fixnum_traits_val, code_traits_val, float_traits_val,
            assoc_map_val, dictionary_map_val,
        ] {
            let map = &mut *(map_val.ref_bits() as *mut object::Map);
            debug_assert_eq!(map.code, NIL_PLACEHOLDER);
            map.code = nil_val;
        }

        let special = SpecialObjects {
            nil: nil_val,
            true_obj: true_val,
            false_obj: false_val,
            map_map: map_map_val,
            array_traits: array_traits_val,
            bytearray_traits: bytearray_traits_val,
            bignum_traits: bignum_traits_val,
            alien_traits: alien_traits_val,
            string_traits: string_traits_val,
            ratio_traits: ratio_traits_val,
            fixnum_traits: fixnum_traits_val,
            code_traits: code_traits_val,
            float_traits: float_traits_val,
        };

        VM {
            heap_proxy: proxy,
            special,
            intern_table: HashMap::new(),
            assoc_map: assoc_map_val,
            dictionary: dictionary_val,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use object::{ObjectType, Map, SlotObject};

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

    #[test]
    fn bootstrap_produces_valid_objects() {
        let vm = bootstrap(test_settings());

        // All special values must be heap references
        assert!(vm.special.nil.is_ref());
        assert!(vm.special.true_obj.is_ref());
        assert!(vm.special.false_obj.is_ref());
        assert!(vm.special.map_map.is_ref());
        assert!(vm.special.array_traits.is_ref());
        assert!(vm.special.bytearray_traits.is_ref());
        assert!(vm.special.bignum_traits.is_ref());
        assert!(vm.special.alien_traits.is_ref());
        assert!(vm.special.string_traits.is_ref());
        assert!(vm.special.ratio_traits.is_ref());
        assert!(vm.special.fixnum_traits.is_ref());
        assert!(vm.special.code_traits.is_ref());

        unsafe {
            // map_map is self-referential
            let map_map: &Map = vm.special.map_map.as_ref();
            assert_eq!(map_map.header.object_type(), ObjectType::Map);
            assert_eq!(map_map.map, vm.special.map_map);
            assert_eq!(map_map.slot_count(), 0);
            assert_eq!(map_map.value_count(), 0);

            // map_map.code was patched from NIL_PLACEHOLDER to real nil
            assert_eq!(map_map.code, vm.special.nil);

            // nil is a SlotObject whose map's map is map_map
            let nil: &SlotObject = vm.special.nil.as_ref();
            assert_eq!(nil.header.object_type(), ObjectType::Slots);
            assert!(nil.map.is_ref());
            let nil_map: &Map = nil.map.as_ref();
            assert_eq!(nil_map.map, vm.special.map_map);
            assert_eq!(nil_map.code, vm.special.nil);

            // true_obj
            let true_obj: &SlotObject = vm.special.true_obj.as_ref();
            assert_eq!(true_obj.header.object_type(), ObjectType::Slots);

            // false_obj
            let false_obj: &SlotObject = vm.special.false_obj.as_ref();
            assert_eq!(false_obj.header.object_type(), ObjectType::Slots);

            // trait maps all point to map_map, code patched to nil
            let arr_traits: &Map = vm.special.array_traits.as_ref();
            assert_eq!(arr_traits.map, vm.special.map_map);
            assert_eq!(arr_traits.code, vm.special.nil);
            assert_eq!(arr_traits.header.object_type(), ObjectType::Map);
        }
    }

    #[test]
    fn bootstrap_nil_true_false_are_distinct() {
        let vm = bootstrap(test_settings());
        assert_ne!(vm.special.nil, vm.special.true_obj);
        assert_ne!(vm.special.nil, vm.special.false_obj);
        assert_ne!(vm.special.true_obj, vm.special.false_obj);
    }
}
