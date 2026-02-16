use std::collections::HashMap;
use std::mem::size_of;

use heap::{Heap, HeapProxy, HeapSettings, RootProvider};
use object::{init_str, MapFlags, SpecialObjects, VMString, Value};

use crate::alloc::{
    add_constant_slot, alloc_byte_array, alloc_map, alloc_slot_object,
};
use crate::primitives;
use crate::{trace_object, VM};

/// Temporary root provider used during bootstrap.
struct BootstrapRoots {
    roots: Vec<Value>,
}

impl BootstrapRoots {
    fn new() -> Self {
        Self {
            roots: Vec::with_capacity(16),
        }
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

unsafe fn alloc_vm_string(
    proxy: &mut HeapProxy,
    roots: &mut BootstrapRoots,
    bytes: &[u8],
) -> Value {
    let mut data = Vec::with_capacity(bytes.len() + 1);
    data.extend_from_slice(bytes);
    data.push(0);
    let ba = alloc_byte_array(proxy, roots, &data).value();
    roots.push(ba);

    let size = size_of::<VMString>();
    let layout = std::alloc::Layout::from_size_align(size, 8).unwrap();
    let ptr = proxy.allocate(layout, roots);
    let str_ptr = ptr.as_ptr() as *mut VMString;
    init_str(str_ptr, bytes.len() as u64, ba);
    Value::from_ptr(str_ptr)
}

unsafe fn intern_bootstrap(
    proxy: &mut HeapProxy,
    roots: &mut BootstrapRoots,
    table: &mut HashMap<String, Value>,
    name: &str,
) -> Value {
    if let Some(&value) = table.get(name) {
        return value;
    }
    let value = alloc_vm_string(proxy, roots, name.as_bytes());
    roots.push(value);
    table.insert(name.to_string(), value);
    value
}

unsafe fn add_dictionary_entry(
    proxy: &mut HeapProxy,
    roots: &mut BootstrapRoots,
    map_map: Value,
    assoc_map: Value,
    dictionary: Value,
    name: Value,
    value: Value,
) {
    let assoc = alloc_slot_object(proxy, roots, assoc_map, &[value]).value();
    roots.push(assoc);

    let dict_obj: &mut object::SlotObject =
        &mut *(dictionary.ref_bits() as *mut object::SlotObject);
    let old_map = dict_obj.map;
    let new_map =
        add_constant_slot(proxy, roots, old_map, map_map, name, assoc);
    roots.push(new_map);
    dict_obj.map = new_map;
}

/// The None value used as a placeholder before real None is allocated.
const NONE_PLACEHOLDER: Value = Value::from_raw(0);

/// Bootstrap the VM by allocating all special objects.
///
/// Creates the heap, allocates `map_map` (self-referential), `None`, `true`,
/// `false`, and all trait maps for primitive types, then returns a fully
/// initialized [`VM`].
pub fn bootstrap(settings: HeapSettings) -> VM {
    let heap = Heap::new(settings, trace_object);
    let mut proxy = heap.proxy();
    let mut roots = BootstrapRoots::new();
    let mut intern_table = HashMap::new();
    let primitives = primitives::default_primitives();

    unsafe {
        // 1. map_map — 0-slot Map, temporarily None map ptr, then patch self-referential
        let map_map_val = alloc_map(
            &mut proxy,
            &mut roots,
            NONE_PLACEHOLDER,
            NONE_PLACEHOLDER,
            MapFlags::NONE,
            &[],
            0,
        )
        .value();
        (*(map_map_val.ref_bits() as *mut object::Map)).map = map_map_val;
        roots.push(map_map_val);

        // 2. none_map + None
        let none_map_val = alloc_map(
            &mut proxy,
            &mut roots,
            map_map_val,
            NONE_PLACEHOLDER,
            MapFlags::NONE,
            &[],
            0,
        )
        .value();
        roots.push(none_map_val);

        let none_val =
            alloc_slot_object(&mut proxy, &mut roots, none_map_val, &[])
                .value();
        roots.push(none_val);

        // 3. true_map + true_obj
        let true_map_val = alloc_map(
            &mut proxy,
            &mut roots,
            map_map_val,
            NONE_PLACEHOLDER,
            MapFlags::NONE,
            &[],
            0,
        )
        .value();
        roots.push(true_map_val);

        let true_val =
            alloc_slot_object(&mut proxy, &mut roots, true_map_val, &[])
                .value();
        roots.push(true_val);

        // 4. false_map + false_obj
        let false_map_val = alloc_map(
            &mut proxy,
            &mut roots,
            map_map_val,
            NONE_PLACEHOLDER,
            MapFlags::NONE,
            &[],
            0,
        )
        .value();
        roots.push(false_map_val);

        let false_val =
            alloc_slot_object(&mut proxy, &mut roots, false_map_val, &[])
                .value();
        roots.push(false_val);

        // 5. Trait maps + objects for primitive types
        let array_traits_map_val = alloc_map(
            &mut proxy,
            &mut roots,
            map_map_val,
            NONE_PLACEHOLDER,
            MapFlags::NONE,
            &[],
            0,
        )
        .value();
        roots.push(array_traits_map_val);
        let array_traits_val = alloc_slot_object(
            &mut proxy,
            &mut roots,
            array_traits_map_val,
            &[],
        )
        .value();
        roots.push(array_traits_val);

        let mut bytearray_traits_map_val = alloc_map(
            &mut proxy,
            &mut roots,
            map_map_val,
            NONE_PLACEHOLDER,
            MapFlags::NONE,
            &[],
            0,
        )
        .value();
        roots.push(bytearray_traits_map_val);
        let bytearray_traits_val = alloc_slot_object(
            &mut proxy,
            &mut roots,
            bytearray_traits_map_val,
            &[],
        )
        .value();
        roots.push(bytearray_traits_val);

        let mut bignum_traits_map_val = alloc_map(
            &mut proxy,
            &mut roots,
            map_map_val,
            NONE_PLACEHOLDER,
            MapFlags::NONE,
            &[],
            0,
        )
        .value();
        roots.push(bignum_traits_map_val);
        let bignum_traits_val = alloc_slot_object(
            &mut proxy,
            &mut roots,
            bignum_traits_map_val,
            &[],
        )
        .value();
        roots.push(bignum_traits_val);

        let alien_traits_map_val = alloc_map(
            &mut proxy,
            &mut roots,
            map_map_val,
            NONE_PLACEHOLDER,
            MapFlags::NONE,
            &[],
            0,
        )
        .value();
        roots.push(alien_traits_map_val);
        let alien_traits_val = alloc_slot_object(
            &mut proxy,
            &mut roots,
            alien_traits_map_val,
            &[],
        )
        .value();
        roots.push(alien_traits_val);

        let mut string_traits_map_val = alloc_map(
            &mut proxy,
            &mut roots,
            map_map_val,
            NONE_PLACEHOLDER,
            MapFlags::NONE,
            &[],
            0,
        )
        .value();
        roots.push(string_traits_map_val);
        let string_traits_val = alloc_slot_object(
            &mut proxy,
            &mut roots,
            string_traits_map_val,
            &[],
        )
        .value();
        roots.push(string_traits_val);

        let mut ratio_traits_map_val = alloc_map(
            &mut proxy,
            &mut roots,
            map_map_val,
            NONE_PLACEHOLDER,
            MapFlags::NONE,
            &[],
            0,
        )
        .value();
        roots.push(ratio_traits_map_val);
        let ratio_traits_val = alloc_slot_object(
            &mut proxy,
            &mut roots,
            ratio_traits_map_val,
            &[],
        )
        .value();
        roots.push(ratio_traits_val);

        let mut fixnum_traits_map_val = alloc_map(
            &mut proxy,
            &mut roots,
            map_map_val,
            NONE_PLACEHOLDER,
            MapFlags::NONE,
            &[],
            0,
        )
        .value();
        roots.push(fixnum_traits_map_val);
        let fixnum_traits_val = alloc_slot_object(
            &mut proxy,
            &mut roots,
            fixnum_traits_map_val,
            &[],
        )
        .value();
        roots.push(fixnum_traits_val);

        let code_traits_map_val = alloc_map(
            &mut proxy,
            &mut roots,
            map_map_val,
            NONE_PLACEHOLDER,
            MapFlags::NONE,
            &[],
            0,
        )
        .value();
        roots.push(code_traits_map_val);
        let code_traits_val =
            alloc_slot_object(&mut proxy, &mut roots, code_traits_map_val, &[])
                .value();
        roots.push(code_traits_val);

        let mut float_traits_map_val = alloc_map(
            &mut proxy,
            &mut roots,
            map_map_val,
            NONE_PLACEHOLDER,
            MapFlags::NONE,
            &[],
            0,
        )
        .value();
        roots.push(float_traits_map_val);
        let float_traits_val = alloc_slot_object(
            &mut proxy,
            &mut roots,
            float_traits_map_val,
            &[],
        )
        .value();
        roots.push(float_traits_val);

        let mut block_traits_map_val = alloc_map(
            &mut proxy,
            &mut roots,
            map_map_val,
            NONE_PLACEHOLDER,
            MapFlags::NONE,
            &[],
            0,
        )
        .value();
        roots.push(block_traits_map_val);
        let block_traits_val = alloc_slot_object(
            &mut proxy,
            &mut roots,
            block_traits_map_val,
            &[],
        )
        .value();
        roots.push(block_traits_val);

        // 6. assoc_map: 0 named slots, value_count=1 (one inline value per assoc)
        let assoc_map_val = alloc_map(
            &mut proxy,
            &mut roots,
            map_map_val,
            NONE_PLACEHOLDER,
            MapFlags::NONE,
            &[],
            1,
        )
        .value();
        roots.push(assoc_map_val);

        // 7. dictionary_map + dictionary: empty SlotObject with 0-slot map
        let dictionary_map_val = alloc_map(
            &mut proxy,
            &mut roots,
            map_map_val,
            NONE_PLACEHOLDER,
            MapFlags::NONE,
            &[],
            0,
        )
        .value();
        roots.push(dictionary_map_val);

        let dictionary_val =
            alloc_slot_object(&mut proxy, &mut roots, dictionary_map_val, &[])
                .value();
        roots.push(dictionary_val);

        // 8. Primitive methods
        let fixnum_primitives = [
            ("fixnum_add", "_FixnumAdd:"),
            ("fixnum_sub", "_FixnumSub:"),
            ("fixnum_mul", "_FixnumMul:"),
            ("fixnum_div", "_FixnumDiv:"),
            ("fixnum_mod", "_FixnumMod:"),
            ("fixnum_neg", "_FixnumNeg"),
            ("fixnum_to_bignum", "_FixnumToBignum"),
            ("fixnum_to_ratio", "_FixnumToRatio"),
            ("fixnum_to_float", "_FixnumToFloat"),
            ("fixnum_to_string", "_FixnumToString"),
            ("fixnum_to_string_radix", "_FixnumToStringRadix:"),
            ("fixnum_eq", "_FixnumEq:"),
            ("fixnum_ne", "_FixnumNe:"),
            ("fixnum_lt", "_FixnumLt:"),
            ("fixnum_le", "_FixnumLe:"),
            ("fixnum_gt", "_FixnumGt:"),
            ("fixnum_ge", "_FixnumGe:"),
        ];

        for (prim_name, slot_name) in fixnum_primitives {
            let prim_idx =
                primitives::primitive_index_by_name(&primitives, prim_name)
                    .expect("fixnum primitive missing") as i64;
            let slot_value = intern_bootstrap(
                &mut proxy,
                &mut roots,
                &mut intern_table,
                slot_name,
            );

            let primitive_code = Value::from_i64(prim_idx);
            let method_map_val = alloc_map(
                &mut proxy,
                &mut roots,
                map_map_val,
                primitive_code,
                MapFlags::HAS_CODE.with(MapFlags::PRIMITIVE),
                &[],
                0,
            )
            .value();
            roots.push(method_map_val);

            let method_obj_val =
                alloc_slot_object(&mut proxy, &mut roots, method_map_val, &[])
                    .value();
            roots.push(method_obj_val);

            let new_fixnum_traits_map = add_constant_slot(
                &mut proxy,
                &mut roots,
                fixnum_traits_map_val,
                map_map_val,
                slot_value,
                method_obj_val,
            );
            roots.push(new_fixnum_traits_map);
            fixnum_traits_map_val = new_fixnum_traits_map;
            let fixnum_traits_obj_ptr =
                fixnum_traits_val.ref_bits() as *mut object::SlotObject;
            (*fixnum_traits_obj_ptr).map = fixnum_traits_map_val;
        }

        let bignum_primitives = [
            ("bignum_add", "_BignumAdd:"),
            ("bignum_sub", "_BignumSub:"),
            ("bignum_mul", "_BignumMul:"),
            ("bignum_div", "_BignumDiv:"),
            ("bignum_mod", "_BignumMod:"),
            ("bignum_neg", "_BignumNeg"),
            ("bignum_to_fixnum", "_BignumToFixnum"),
            ("bignum_to_ratio", "_BignumToRatio"),
            ("bignum_to_float", "_BignumToFloat"),
            ("bignum_to_string", "_BignumToString"),
            ("bignum_eq", "_BignumEq:"),
            ("bignum_ne", "_BignumNe:"),
            ("bignum_lt", "_BignumLt:"),
            ("bignum_le", "_BignumLe:"),
            ("bignum_gt", "_BignumGt:"),
            ("bignum_ge", "_BignumGe:"),
        ];

        for (prim_name, slot_name) in bignum_primitives {
            let prim_idx =
                primitives::primitive_index_by_name(&primitives, prim_name)
                    .expect("bignum primitive missing") as i64;
            let slot_value = intern_bootstrap(
                &mut proxy,
                &mut roots,
                &mut intern_table,
                slot_name,
            );

            let primitive_code = Value::from_i64(prim_idx);
            let method_map_val = alloc_map(
                &mut proxy,
                &mut roots,
                map_map_val,
                primitive_code,
                MapFlags::HAS_CODE.with(MapFlags::PRIMITIVE),
                &[],
                0,
            )
            .value();
            roots.push(method_map_val);

            let method_obj_val =
                alloc_slot_object(&mut proxy, &mut roots, method_map_val, &[])
                    .value();
            roots.push(method_obj_val);

            let new_bignum_traits_map = add_constant_slot(
                &mut proxy,
                &mut roots,
                bignum_traits_map_val,
                map_map_val,
                slot_value,
                method_obj_val,
            );
            roots.push(new_bignum_traits_map);
            bignum_traits_map_val = new_bignum_traits_map;
            let bignum_traits_obj_ptr =
                bignum_traits_val.ref_bits() as *mut object::SlotObject;
            (*bignum_traits_obj_ptr).map = bignum_traits_map_val;
        }

        let ratio_primitives = [
            ("ratio_add", "_RatioAdd:"),
            ("ratio_sub", "_RatioSub:"),
            ("ratio_mul", "_RatioMul:"),
            ("ratio_div", "_RatioDiv:"),
            ("ratio_neg", "_RatioNeg"),
            ("ratio_numerator", "_RatioNumerator"),
            ("ratio_denominator", "_RatioDenominator"),
            ("ratio_to_fixnum", "_RatioToFixnum"),
            ("ratio_to_bignum", "_RatioToBignum"),
            ("ratio_to_float", "_RatioToFloat"),
            ("ratio_to_string", "_RatioToString"),
            ("ratio_eq", "_RatioEq:"),
            ("ratio_ne", "_RatioNe:"),
            ("ratio_lt", "_RatioLt:"),
            ("ratio_le", "_RatioLe:"),
            ("ratio_gt", "_RatioGt:"),
            ("ratio_ge", "_RatioGe:"),
        ];

        for (prim_name, slot_name) in ratio_primitives {
            let prim_idx =
                primitives::primitive_index_by_name(&primitives, prim_name)
                    .expect("ratio primitive missing") as i64;
            let slot_value = intern_bootstrap(
                &mut proxy,
                &mut roots,
                &mut intern_table,
                slot_name,
            );

            let primitive_code = Value::from_i64(prim_idx);
            let method_map_val = alloc_map(
                &mut proxy,
                &mut roots,
                map_map_val,
                primitive_code,
                MapFlags::HAS_CODE.with(MapFlags::PRIMITIVE),
                &[],
                0,
            )
            .value();
            roots.push(method_map_val);

            let method_obj_val =
                alloc_slot_object(&mut proxy, &mut roots, method_map_val, &[])
                    .value();
            roots.push(method_obj_val);

            let new_ratio_traits_map = add_constant_slot(
                &mut proxy,
                &mut roots,
                ratio_traits_map_val,
                map_map_val,
                slot_value,
                method_obj_val,
            );
            roots.push(new_ratio_traits_map);
            ratio_traits_map_val = new_ratio_traits_map;
            let ratio_traits_obj_ptr =
                ratio_traits_val.ref_bits() as *mut object::SlotObject;
            (*ratio_traits_obj_ptr).map = ratio_traits_map_val;
        }

        let float_primitives = [
            ("float_add", "_FloatAdd:"),
            ("float_sub", "_FloatSub:"),
            ("float_mul", "_FloatMul:"),
            ("float_div", "_FloatDiv:"),
            ("float_mod", "_FloatMod:"),
            ("float_neg", "_FloatNeg"),
            ("float_to_fixnum", "_FloatToFixnum"),
            ("float_to_bignum", "_FloatToBignum"),
            ("float_to_ratio", "_FloatToRatio"),
            ("float_to_string", "_FloatToString"),
            ("float_to_string_digits", "_FloatToStringDigits:"),
            ("float_eq", "_FloatEq:"),
            ("float_ne", "_FloatNe:"),
            ("float_lt", "_FloatLt:"),
            ("float_le", "_FloatLe:"),
            ("float_gt", "_FloatGt:"),
            ("float_ge", "_FloatGe:"),
            ("float_approx_eq", "_FloatApproxEq:WithEpsilon:"),
        ];

        for (prim_name, slot_name) in float_primitives {
            let prim_idx =
                primitives::primitive_index_by_name(&primitives, prim_name)
                    .expect("float primitive missing") as i64;
            let slot_value = intern_bootstrap(
                &mut proxy,
                &mut roots,
                &mut intern_table,
                slot_name,
            );

            let primitive_code = Value::from_i64(prim_idx);
            let method_map_val = alloc_map(
                &mut proxy,
                &mut roots,
                map_map_val,
                primitive_code,
                MapFlags::HAS_CODE.with(MapFlags::PRIMITIVE),
                &[],
                0,
            )
            .value();
            roots.push(method_map_val);

            let method_obj_val =
                alloc_slot_object(&mut proxy, &mut roots, method_map_val, &[])
                    .value();
            roots.push(method_obj_val);

            let new_float_traits_map = add_constant_slot(
                &mut proxy,
                &mut roots,
                float_traits_map_val,
                map_map_val,
                slot_value,
                method_obj_val,
            );
            roots.push(new_float_traits_map);
            float_traits_map_val = new_float_traits_map;
            let float_traits_obj_ptr =
                float_traits_val.ref_bits() as *mut object::SlotObject;
            (*float_traits_obj_ptr).map = float_traits_map_val;
        }

        let block_primitives = [
            ("block_call0", "call"),
            ("block_call1", "call:"),
            ("block_call2", "call:With:"),
            ("block_call3", "call:With:With:"),
            ("block_call4", "call:With:With:With:"),
            ("block_call5", "call:With:With:With:With:"),
            ("block_call6", "call:With:With:With:With:With:"),
            ("block_call7", "call:With:With:With:With:With:With:"),
            ("block_call8", "call:With:With:With:With:With:With:With:"),
        ];

        for (prim_name, slot_name) in block_primitives {
            let prim_idx =
                primitives::primitive_index_by_name(&primitives, prim_name)
                    .expect("block primitive missing") as i64;
            let slot_value = intern_bootstrap(
                &mut proxy,
                &mut roots,
                &mut intern_table,
                slot_name,
            );

            let primitive_code = Value::from_i64(prim_idx);
            let method_map_val = alloc_map(
                &mut proxy,
                &mut roots,
                map_map_val,
                primitive_code,
                MapFlags::HAS_CODE.with(MapFlags::PRIMITIVE),
                &[],
                0,
            )
            .value();
            roots.push(method_map_val);

            let method_obj_val =
                alloc_slot_object(&mut proxy, &mut roots, method_map_val, &[])
                    .value();
            roots.push(method_obj_val);

            let new_block_traits_map = add_constant_slot(
                &mut proxy,
                &mut roots,
                block_traits_map_val,
                map_map_val,
                slot_value,
                method_obj_val,
            );
            roots.push(new_block_traits_map);
            block_traits_map_val = new_block_traits_map;
            let block_traits_obj_ptr =
                block_traits_val.ref_bits() as *mut object::SlotObject;
            (*block_traits_obj_ptr).map = block_traits_map_val;
        }

        let string_primitives = [
            ("string_print", "_Print"),
            ("string_println", "_PrintLn"),
            ("string_length", "_StringLength"),
            ("string_to_bytearray", "_StringToByteArray"),
        ];

        for (prim_name, slot_name) in string_primitives {
            let prim_idx =
                primitives::primitive_index_by_name(&primitives, prim_name)
                    .expect("string primitive missing") as i64;
            let slot_value = intern_bootstrap(
                &mut proxy,
                &mut roots,
                &mut intern_table,
                slot_name,
            );

            let primitive_code = Value::from_i64(prim_idx);
            let method_map_val = alloc_map(
                &mut proxy,
                &mut roots,
                map_map_val,
                primitive_code,
                MapFlags::HAS_CODE.with(MapFlags::PRIMITIVE),
                &[],
                0,
            )
            .value();
            roots.push(method_map_val);

            let method_obj_val =
                alloc_slot_object(&mut proxy, &mut roots, method_map_val, &[])
                    .value();
            roots.push(method_obj_val);

            let new_string_traits_map = add_constant_slot(
                &mut proxy,
                &mut roots,
                string_traits_map_val,
                map_map_val,
                slot_value,
                method_obj_val,
            );
            roots.push(new_string_traits_map);
            string_traits_map_val = new_string_traits_map;
            let string_traits_obj_ptr =
                string_traits_val.ref_bits() as *mut object::SlotObject;
            (*string_traits_obj_ptr).map = string_traits_map_val;
        }

        let bytearray_primitives = [("bytearray_size", "_ByteArraySize")];
        for (prim_name, slot_name) in bytearray_primitives {
            let prim_idx =
                primitives::primitive_index_by_name(&primitives, prim_name)
                    .expect("bytearray primitive missing")
                    as i64;
            let slot_value = intern_bootstrap(
                &mut proxy,
                &mut roots,
                &mut intern_table,
                slot_name,
            );

            let primitive_code = Value::from_i64(prim_idx);
            let method_map_val = alloc_map(
                &mut proxy,
                &mut roots,
                map_map_val,
                primitive_code,
                MapFlags::HAS_CODE.with(MapFlags::PRIMITIVE),
                &[],
                0,
            )
            .value();
            roots.push(method_map_val);

            let method_obj_val =
                alloc_slot_object(&mut proxy, &mut roots, method_map_val, &[])
                    .value();
            roots.push(method_obj_val);

            let new_bytearray_traits_map = add_constant_slot(
                &mut proxy,
                &mut roots,
                bytearray_traits_map_val,
                map_map_val,
                slot_value,
                method_obj_val,
            );
            roots.push(new_bytearray_traits_map);
            bytearray_traits_map_val = new_bytearray_traits_map;
            let bytearray_traits_obj_ptr =
                bytearray_traits_val.ref_bits() as *mut object::SlotObject;
            (*bytearray_traits_obj_ptr).map = bytearray_traits_map_val;
        }

        let fixnum_name = intern_bootstrap(
            &mut proxy,
            &mut roots,
            &mut intern_table,
            "Fixnum",
        );
        add_dictionary_entry(
            &mut proxy,
            &mut roots,
            map_map_val,
            assoc_map_val,
            dictionary_val,
            fixnum_name,
            fixnum_traits_val,
        );

        let bignum_name = intern_bootstrap(
            &mut proxy,
            &mut roots,
            &mut intern_table,
            "Bignum",
        );
        add_dictionary_entry(
            &mut proxy,
            &mut roots,
            map_map_val,
            assoc_map_val,
            dictionary_val,
            bignum_name,
            bignum_traits_val,
        );

        let ratio_name = intern_bootstrap(
            &mut proxy,
            &mut roots,
            &mut intern_table,
            "Ratio",
        );
        add_dictionary_entry(
            &mut proxy,
            &mut roots,
            map_map_val,
            assoc_map_val,
            dictionary_val,
            ratio_name,
            ratio_traits_val,
        );

        let float_name = intern_bootstrap(
            &mut proxy,
            &mut roots,
            &mut intern_table,
            "Float",
        );
        add_dictionary_entry(
            &mut proxy,
            &mut roots,
            map_map_val,
            assoc_map_val,
            dictionary_val,
            float_name,
            float_traits_val,
        );

        let array_name = intern_bootstrap(
            &mut proxy,
            &mut roots,
            &mut intern_table,
            "Array",
        );
        add_dictionary_entry(
            &mut proxy,
            &mut roots,
            map_map_val,
            assoc_map_val,
            dictionary_val,
            array_name,
            array_traits_val,
        );

        let bytearray_name = intern_bootstrap(
            &mut proxy,
            &mut roots,
            &mut intern_table,
            "ByteArray",
        );
        add_dictionary_entry(
            &mut proxy,
            &mut roots,
            map_map_val,
            assoc_map_val,
            dictionary_val,
            bytearray_name,
            bytearray_traits_val,
        );

        let string_name = intern_bootstrap(
            &mut proxy,
            &mut roots,
            &mut intern_table,
            "String",
        );
        add_dictionary_entry(
            &mut proxy,
            &mut roots,
            map_map_val,
            assoc_map_val,
            dictionary_val,
            string_name,
            string_traits_val,
        );

        let extend_idx =
            primitives::primitive_index_by_name(&primitives, "extend_with")
                .expect("extend_with primitive missing") as i64;
        let extend_name = intern_bootstrap(
            &mut proxy,
            &mut roots,
            &mut intern_table,
            "_Extend:With:",
        );

        let object_map_val = alloc_map(
            &mut proxy,
            &mut roots,
            map_map_val,
            NONE_PLACEHOLDER,
            MapFlags::NONE,
            &[],
            0,
        )
        .value();
        roots.push(object_map_val);

        let object_val =
            alloc_slot_object(&mut proxy, &mut roots, object_map_val, &[])
                .value();
        roots.push(object_val);

        let extend_code = Value::from_i64(extend_idx);
        let extend_map_val = alloc_map(
            &mut proxy,
            &mut roots,
            map_map_val,
            extend_code,
            MapFlags::HAS_CODE.with(MapFlags::PRIMITIVE),
            &[],
            0,
        )
        .value();
        roots.push(extend_map_val);

        let extend_method_val =
            alloc_slot_object(&mut proxy, &mut roots, extend_map_val, &[])
                .value();
        roots.push(extend_method_val);

        let new_object_map = add_constant_slot(
            &mut proxy,
            &mut roots,
            object_map_val,
            map_map_val,
            extend_name,
            extend_method_val,
        );
        roots.push(new_object_map);
        let obj_ptr = object_val.ref_bits() as *mut object::SlotObject;
        (*obj_ptr).map = new_object_map;

        let object_name = intern_bootstrap(
            &mut proxy,
            &mut roots,
            &mut intern_table,
            "Object",
        );
        add_dictionary_entry(
            &mut proxy,
            &mut roots,
            map_map_val,
            assoc_map_val,
            dictionary_val,
            object_name,
            object_val,
        );

        let block_name = intern_bootstrap(
            &mut proxy,
            &mut roots,
            &mut intern_table,
            "Block",
        );
        add_dictionary_entry(
            &mut proxy,
            &mut roots,
            map_map_val,
            assoc_map_val,
            dictionary_val,
            block_name,
            block_traits_val,
        );

        let true_name =
            intern_bootstrap(&mut proxy, &mut roots, &mut intern_table, "true");
        add_dictionary_entry(
            &mut proxy,
            &mut roots,
            map_map_val,
            assoc_map_val,
            dictionary_val,
            true_name,
            true_val,
        );

        let false_name = intern_bootstrap(
            &mut proxy,
            &mut roots,
            &mut intern_table,
            "false",
        );
        add_dictionary_entry(
            &mut proxy,
            &mut roots,
            map_map_val,
            assoc_map_val,
            dictionary_val,
            false_name,
            false_val,
        );

        let none_name =
            intern_bootstrap(&mut proxy, &mut roots, &mut intern_table, "none");
        add_dictionary_entry(
            &mut proxy,
            &mut roots,
            map_map_val,
            assoc_map_val,
            dictionary_val,
            none_name,
            none_val,
        );

        // 9. Fixup: patch NONE_PLACEHOLDER → real None in every map's `code` field
        for &map_val in &[
            map_map_val,
            none_map_val,
            true_map_val,
            false_map_val,
            array_traits_map_val,
            bytearray_traits_map_val,
            bignum_traits_map_val,
            alien_traits_map_val,
            string_traits_map_val,
            ratio_traits_map_val,
            fixnum_traits_map_val,
            code_traits_map_val,
            float_traits_map_val,
            block_traits_map_val,
            object_map_val,
            new_object_map,
            assoc_map_val,
            dictionary_map_val,
        ] {
            let map = &mut *(map_val.ref_bits() as *mut object::Map);
            debug_assert_eq!(map.code, NONE_PLACEHOLDER);
            map.code = none_val;
        }

        let special = SpecialObjects {
            none: none_val,
            true_obj: true_val,
            false_obj: false_val,
            map_map: map_map_val,
            object: object_val,
            block_traits: block_traits_val,
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
            intern_table,
            primitives,
            assoc_map: assoc_map_val,
            dictionary: dictionary_val,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use object::{Map, ObjectType, SlotObject};

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
        assert!(vm.special.none.is_ref());
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

            // map_map.code was patched from NONE_PLACEHOLDER to real None
            assert_eq!(map_map.code, vm.special.none);

            // None is a SlotObject whose map's map is map_map
            let none: &SlotObject = vm.special.none.as_ref();
            assert_eq!(none.header.object_type(), ObjectType::Slots);
            assert!(none.map.is_ref());
            let none_map: &Map = none.map.as_ref();
            assert_eq!(none_map.map, vm.special.map_map);
            assert_eq!(none_map.code, vm.special.none);

            // true_obj
            let true_obj: &SlotObject = vm.special.true_obj.as_ref();
            assert_eq!(true_obj.header.object_type(), ObjectType::Slots);

            // false_obj
            let false_obj: &SlotObject = vm.special.false_obj.as_ref();
            assert_eq!(false_obj.header.object_type(), ObjectType::Slots);

            // trait maps all point to map_map, code patched to None
            let arr_traits: &SlotObject = vm.special.array_traits.as_ref();
            let arr_map: &Map = arr_traits.map.as_ref();
            assert_eq!(arr_map.map, vm.special.map_map);
            assert_eq!(arr_map.code, vm.special.none);
            assert_eq!(arr_traits.header.object_type(), ObjectType::Slots);

            let object_obj: &SlotObject = vm.special.object.as_ref();
            assert_eq!(object_obj.header.object_type(), ObjectType::Slots);

            let block_obj: &SlotObject = vm.special.block_traits.as_ref();
            assert_eq!(block_obj.header.object_type(), ObjectType::Slots);
        }
    }

    #[test]
    fn bootstrap_none_true_false_are_distinct() {
        let vm = bootstrap(test_settings());
        assert_ne!(vm.special.none, vm.special.true_obj);
        assert_ne!(vm.special.none, vm.special.false_obj);
        assert_ne!(vm.special.true_obj, vm.special.false_obj);
    }
}
