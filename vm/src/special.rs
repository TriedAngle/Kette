use std::collections::HashMap;
use std::mem::size_of;

use heap::{Heap, HeapProxy, HeapSettings, RootProvider};
use object::{
    init_symbol, MapFlags, Slot, SlotFlags, SpecialObjects, VMSymbol, Value,
};

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

unsafe fn alloc_vm_symbol(
    proxy: &mut HeapProxy,
    roots: &mut BootstrapRoots,
    bytes: &[u8],
) -> Value {
    let mut data = Vec::with_capacity(bytes.len() + 1);
    data.extend_from_slice(bytes);
    data.push(0);
    let ba = alloc_byte_array(proxy, roots, &data).value();
    roots.push(ba);

    let size = size_of::<VMSymbol>();
    let layout = std::alloc::Layout::from_size_align(size, 8).unwrap();
    let ptr = proxy.allocate(layout, roots);
    let sym_ptr = ptr.as_ptr() as *mut VMSymbol;
    init_symbol(sym_ptr, bytes.len() as u64, ba);
    Value::from_ptr(sym_ptr)
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
    let value = alloc_vm_symbol(proxy, roots, name.as_bytes());
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
    let heap = Heap::new(settings, trace_object, crate::OBJECT_SIZE_FN);
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

        let mut alien_traits_map_val = alloc_map(
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

        let mut symbol_traits_map_val = alloc_map(
            &mut proxy,
            &mut roots,
            map_map_val,
            NONE_PLACEHOLDER,
            MapFlags::NONE,
            &[],
            0,
        )
        .value();
        roots.push(symbol_traits_map_val);
        let symbol_traits_val = alloc_slot_object(
            &mut proxy,
            &mut roots,
            symbol_traits_map_val,
            &[],
        )
        .value();
        roots.push(symbol_traits_val);

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
            ("float_sqrt", "_FloatSqrt"),
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
            ("string_to_symbol", "_StringToSymbol"),
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

        let symbol_primitives = [
            ("symbol_to_string", "_SymbolToString"),
            ("symbol_length", "_SymbolLength"),
        ];

        for (prim_name, slot_name) in symbol_primitives {
            let prim_idx =
                primitives::primitive_index_by_name(&primitives, prim_name)
                    .expect("symbol primitive missing") as i64;
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

            let new_symbol_traits_map = add_constant_slot(
                &mut proxy,
                &mut roots,
                symbol_traits_map_val,
                map_map_val,
                slot_value,
                method_obj_val,
            );
            roots.push(new_symbol_traits_map);
            symbol_traits_map_val = new_symbol_traits_map;
            let symbol_traits_obj_ptr =
                symbol_traits_val.ref_bits() as *mut object::SlotObject;
            (*symbol_traits_obj_ptr).map = symbol_traits_map_val;
        }

        let mut array_traits_map_val = array_traits_map_val;
        let array_primitives = [
            ("array_size", "_ArraySize"),
            ("array_clone_with_size", "_ArrayCloneWithSize:"),
            ("array_at", "_ArrayAt:"),
            ("array_at_put", "_ArrayAt:Put:"),
        ];

        for (prim_name, slot_name) in array_primitives {
            let prim_idx =
                primitives::primitive_index_by_name(&primitives, prim_name)
                    .expect("array primitive missing") as i64;
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

            let new_array_traits_map = add_constant_slot(
                &mut proxy,
                &mut roots,
                array_traits_map_val,
                map_map_val,
                slot_value,
                method_obj_val,
            );
            roots.push(new_array_traits_map);
            array_traits_map_val = new_array_traits_map;
            let array_traits_obj_ptr =
                array_traits_val.ref_bits() as *mut object::SlotObject;
            (*array_traits_obj_ptr).map = array_traits_map_val;
        }

        let bytearray_primitives = [
            ("bytearray_size", "_ByteArraySize"),
            ("bytearray_clone_with_size", "_CloneWithSize:"),
            ("bytearray_memcopy", "_MemCopy:From:To:Length:"),
            (
                "bytearray_memcopy_overlapping",
                "_MemCopyOverlapping:From:To:Length:",
            ),
            ("bytearray_to_string", "_ByteArrayToString"),
            ("bytearray_read_u8", "_ByteArrayU8At:"),
            ("bytearray_read_i8", "_ByteArrayI8At:"),
            ("bytearray_read_u16", "_ByteArrayU16At:"),
            ("bytearray_read_i16", "_ByteArrayI16At:"),
            ("bytearray_read_u32", "_ByteArrayU32At:"),
            ("bytearray_read_i32", "_ByteArrayI32At:"),
            ("bytearray_read_u64", "_ByteArrayU64At:"),
            ("bytearray_read_i64", "_ByteArrayI64At:"),
            ("bytearray_read_f32", "_ByteArrayF32At:"),
            ("bytearray_read_f64", "_ByteArrayF64At:"),
            ("bytearray_read_pointer", "_ByteArrayPointerAt:"),
            ("bytearray_write_u8", "_ByteArrayU8At:Put:"),
            ("bytearray_write_i8", "_ByteArrayI8At:Put:"),
            ("bytearray_write_u16", "_ByteArrayU16At:Put:"),
            ("bytearray_write_i16", "_ByteArrayI16At:Put:"),
            ("bytearray_write_u32", "_ByteArrayU32At:Put:"),
            ("bytearray_write_i32", "_ByteArrayI32At:Put:"),
            ("bytearray_write_u64", "_ByteArrayU64At:Put:"),
            ("bytearray_write_i64", "_ByteArrayI64At:Put:"),
            ("bytearray_write_f32", "_ByteArrayF32At:Put:"),
            ("bytearray_write_f64", "_ByteArrayF64At:Put:"),
            ("bytearray_write_pointer", "_ByteArrayPointerAt:Put:"),
        ];
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

        let alien_primitives = [
            ("alien_new", "_AlienNew:"),
            ("alien_from_address", "_AlienFromAddress:Size:"),
            ("alien_free", "_AlienFree"),
            ("alien_size", "_AlienSize"),
            ("alien_address", "_AlienAddress"),
            ("alien_is_null", "_AlienIsNull"),
            ("alien_read_u8", "_AlienU8At:"),
            ("alien_read_i8", "_AlienI8At:"),
            ("alien_read_u16", "_AlienU16At:"),
            ("alien_read_i16", "_AlienI16At:"),
            ("alien_read_u32", "_AlienU32At:"),
            ("alien_read_i32", "_AlienI32At:"),
            ("alien_read_u64", "_AlienU64At:"),
            ("alien_read_i64", "_AlienI64At:"),
            ("alien_read_f32", "_AlienF32At:"),
            ("alien_read_f64", "_AlienF64At:"),
            ("alien_read_pointer", "_AlienPointerAt:"),
            ("alien_write_u8", "_AlienU8At:Put:"),
            ("alien_write_i8", "_AlienI8At:Put:"),
            ("alien_write_u16", "_AlienU16At:Put:"),
            ("alien_write_i16", "_AlienI16At:Put:"),
            ("alien_write_u32", "_AlienU32At:Put:"),
            ("alien_write_i32", "_AlienI32At:Put:"),
            ("alien_write_u64", "_AlienU64At:Put:"),
            ("alien_write_i64", "_AlienI64At:Put:"),
            ("alien_write_f32", "_AlienF32At:Put:"),
            ("alien_write_f64", "_AlienF64At:Put:"),
            ("alien_write_pointer", "_AlienPointerAt:Put:"),
            ("alien_copy_to_bytearray", "_AlienCopyTo:From:Length:"),
            ("alien_copy_from_bytearray", "_AlienCopyFrom:Offset:Length:"),
            ("alien_library_open", "_LibraryOpen:"),
            ("alien_library_sym", "_LibrarySym:"),
            ("alien_library_close", "_LibraryClose"),
            (
                "alien_call_with_types",
                "_AlienCallWithTypes:Args:ReturnType:",
            ),
        ];

        for (prim_name, slot_name) in alien_primitives {
            let prim_idx =
                primitives::primitive_index_by_name(&primitives, prim_name)
                    .expect("alien primitive missing") as i64;
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

            let new_alien_traits_map = add_constant_slot(
                &mut proxy,
                &mut roots,
                alien_traits_map_val,
                map_map_val,
                slot_value,
                method_obj_val,
            );
            roots.push(new_alien_traits_map);
            alien_traits_map_val = new_alien_traits_map;
            let alien_traits_obj_ptr =
                alien_traits_val.ref_bits() as *mut object::SlotObject;
            (*alien_traits_obj_ptr).map = alien_traits_map_val;
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

        let alien_name = intern_bootstrap(
            &mut proxy,
            &mut roots,
            &mut intern_table,
            "Alien",
        );
        add_dictionary_entry(
            &mut proxy,
            &mut roots,
            map_map_val,
            assoc_map_val,
            dictionary_val,
            alien_name,
            alien_traits_val,
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

        let symbol_name = intern_bootstrap(
            &mut proxy,
            &mut roots,
            &mut intern_table,
            "Symbol",
        );
        add_dictionary_entry(
            &mut proxy,
            &mut roots,
            map_map_val,
            assoc_map_val,
            dictionary_val,
            symbol_name,
            symbol_traits_val,
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

        let clone_idx =
            primitives::primitive_index_by_name(&primitives, "object_clone")
                .expect("object_clone primitive missing") as i64;
        let clone_name = intern_bootstrap(
            &mut proxy,
            &mut roots,
            &mut intern_table,
            "_Clone:",
        );
        let pin_idx =
            primitives::primitive_index_by_name(&primitives, "object_pin")
                .expect("object_pin primitive missing") as i64;
        let pin_name = intern_bootstrap(
            &mut proxy,
            &mut roots,
            &mut intern_table,
            "_Pin:",
        );
        let unpin_idx =
            primitives::primitive_index_by_name(&primitives, "object_unpin")
                .expect("object_unpin primitive missing") as i64;
        let unpin_name = intern_bootstrap(
            &mut proxy,
            &mut roots,
            &mut intern_table,
            "_Unpin:",
        );
        let is_pinned_idx = primitives::primitive_index_by_name(
            &primitives,
            "object_is_pinned",
        )
        .expect("object_is_pinned primitive missing")
            as i64;
        let is_pinned_name = intern_bootstrap(
            &mut proxy,
            &mut roots,
            &mut intern_table,
            "_IsPinned:",
        );
        let reflect_idx =
            primitives::primitive_index_by_name(&primitives, "object_reflect")
                .expect("object_reflect primitive missing") as i64;
        let reflect_name = intern_bootstrap(
            &mut proxy,
            &mut roots,
            &mut intern_table,
            "_Reflect:",
        );
        let ctype_build_struct_idx = primitives::primitive_index_by_name(
            &primitives,
            "ctype_build_struct",
        )
        .expect("ctype_build_struct primitive missing")
            as i64;
        let ctype_build_struct_name = intern_bootstrap(
            &mut proxy,
            &mut roots,
            &mut intern_table,
            "_CTypeBuildStruct:",
        );
        let ctype_field_info_at_idx = primitives::primitive_index_by_name(
            &primitives,
            "ctype_field_info_at",
        )
        .expect("ctype_field_info_at primitive missing")
            as i64;
        let ctype_field_info_at_name = intern_bootstrap(
            &mut proxy,
            &mut roots,
            &mut intern_table,
            "_CTypeFieldInfoAt:",
        );
        let ctype_scalar_tag_idx = primitives::primitive_index_by_name(
            &primitives,
            "ctype_scalar_tag",
        )
        .expect("ctype_scalar_tag primitive missing")
            as i64;
        let ctype_scalar_tag_name = intern_bootstrap(
            &mut proxy,
            &mut roots,
            &mut intern_table,
            "_CTypeScalarTag",
        );
        let become_with_idx = primitives::primitive_index_by_name(
            &primitives,
            "object_become_with",
        )
        .expect("object_become_with primitive missing")
            as i64;
        let become_with_name = intern_bootstrap(
            &mut proxy,
            &mut roots,
            &mut intern_table,
            "_Become:With:",
        );
        let vm_eval_idx =
            primitives::primitive_index_by_name(&primitives, "vm_eval")
                .expect("vm_eval primitive missing") as i64;
        let vm_module_open_idx =
            primitives::primitive_index_by_name(&primitives, "vm_module_open")
                .expect("vm_module_open primitive missing") as i64;
        let vm_module_use_idx =
            primitives::primitive_index_by_name(&primitives, "vm_module_use")
                .expect("vm_module_use primitive missing") as i64;
        let vm_module_use_as_idx = primitives::primitive_index_by_name(
            &primitives,
            "vm_module_use_as",
        )
        .expect("vm_module_use_as primitive missing")
            as i64;
        let vm_module_export_idx = primitives::primitive_index_by_name(
            &primitives,
            "vm_module_export",
        )
        .expect("vm_module_export primitive missing")
            as i64;
        let vm_module_at_idx =
            primitives::primitive_index_by_name(&primitives, "vm_module_at")
                .expect("vm_module_at primitive missing") as i64;
        let vm_current_module_idx = primitives::primitive_index_by_name(
            &primitives,
            "vm_current_module",
        )
        .expect("vm_current_module primitive missing")
            as i64;
        let vm_eval_name = intern_bootstrap(
            &mut proxy,
            &mut roots,
            &mut intern_table,
            "_Eval:",
        );
        let vm_module_open_name = intern_bootstrap(
            &mut proxy,
            &mut roots,
            &mut intern_table,
            "_ModuleOpen:",
        );
        let vm_module_use_name = intern_bootstrap(
            &mut proxy,
            &mut roots,
            &mut intern_table,
            "_ModuleUse:",
        );
        let vm_module_use_as_name = intern_bootstrap(
            &mut proxy,
            &mut roots,
            &mut intern_table,
            "_ModuleUse:As:",
        );
        let vm_module_export_name = intern_bootstrap(
            &mut proxy,
            &mut roots,
            &mut intern_table,
            "_ModuleExport:",
        );
        let vm_module_at_name = intern_bootstrap(
            &mut proxy,
            &mut roots,
            &mut intern_table,
            "_ModuleAt:",
        );
        let vm_current_module_name = intern_bootstrap(
            &mut proxy,
            &mut roots,
            &mut intern_table,
            "_CurrentModule",
        );

        let mut object_map_val = alloc_map(
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
        object_map_val = new_object_map;

        let become_with_code = Value::from_i64(become_with_idx);
        let become_with_map_val = alloc_map(
            &mut proxy,
            &mut roots,
            map_map_val,
            become_with_code,
            MapFlags::HAS_CODE.with(MapFlags::PRIMITIVE),
            &[],
            0,
        )
        .value();
        roots.push(become_with_map_val);

        let become_with_method_val =
            alloc_slot_object(&mut proxy, &mut roots, become_with_map_val, &[])
                .value();
        roots.push(become_with_method_val);

        let new_object_map = add_constant_slot(
            &mut proxy,
            &mut roots,
            object_map_val,
            map_map_val,
            become_with_name,
            become_with_method_val,
        );
        roots.push(new_object_map);
        object_map_val = new_object_map;

        let pin_code = Value::from_i64(pin_idx);
        let pin_map_val = alloc_map(
            &mut proxy,
            &mut roots,
            map_map_val,
            pin_code,
            MapFlags::HAS_CODE.with(MapFlags::PRIMITIVE),
            &[],
            0,
        )
        .value();
        roots.push(pin_map_val);

        let pin_method_val =
            alloc_slot_object(&mut proxy, &mut roots, pin_map_val, &[]).value();
        roots.push(pin_method_val);

        let new_object_map = add_constant_slot(
            &mut proxy,
            &mut roots,
            object_map_val,
            map_map_val,
            pin_name,
            pin_method_val,
        );
        roots.push(new_object_map);
        object_map_val = new_object_map;

        let unpin_code = Value::from_i64(unpin_idx);
        let unpin_map_val = alloc_map(
            &mut proxy,
            &mut roots,
            map_map_val,
            unpin_code,
            MapFlags::HAS_CODE.with(MapFlags::PRIMITIVE),
            &[],
            0,
        )
        .value();
        roots.push(unpin_map_val);

        let unpin_method_val =
            alloc_slot_object(&mut proxy, &mut roots, unpin_map_val, &[])
                .value();
        roots.push(unpin_method_val);

        let new_object_map = add_constant_slot(
            &mut proxy,
            &mut roots,
            object_map_val,
            map_map_val,
            unpin_name,
            unpin_method_val,
        );
        roots.push(new_object_map);
        object_map_val = new_object_map;

        let is_pinned_code = Value::from_i64(is_pinned_idx);
        let is_pinned_map_val = alloc_map(
            &mut proxy,
            &mut roots,
            map_map_val,
            is_pinned_code,
            MapFlags::HAS_CODE.with(MapFlags::PRIMITIVE),
            &[],
            0,
        )
        .value();
        roots.push(is_pinned_map_val);

        let is_pinned_method_val =
            alloc_slot_object(&mut proxy, &mut roots, is_pinned_map_val, &[])
                .value();
        roots.push(is_pinned_method_val);

        let new_object_map = add_constant_slot(
            &mut proxy,
            &mut roots,
            object_map_val,
            map_map_val,
            is_pinned_name,
            is_pinned_method_val,
        );
        roots.push(new_object_map);
        object_map_val = new_object_map;

        let clone_code = Value::from_i64(clone_idx);
        let clone_map_val = alloc_map(
            &mut proxy,
            &mut roots,
            map_map_val,
            clone_code,
            MapFlags::HAS_CODE.with(MapFlags::PRIMITIVE),
            &[],
            0,
        )
        .value();
        roots.push(clone_map_val);

        let clone_method_val =
            alloc_slot_object(&mut proxy, &mut roots, clone_map_val, &[])
                .value();
        roots.push(clone_method_val);

        let new_object_map = add_constant_slot(
            &mut proxy,
            &mut roots,
            object_map_val,
            map_map_val,
            clone_name,
            clone_method_val,
        );
        roots.push(new_object_map);
        object_map_val = new_object_map;

        let reflect_code = Value::from_i64(reflect_idx);
        let reflect_map_val = alloc_map(
            &mut proxy,
            &mut roots,
            map_map_val,
            reflect_code,
            MapFlags::HAS_CODE.with(MapFlags::PRIMITIVE),
            &[],
            0,
        )
        .value();
        roots.push(reflect_map_val);

        let reflect_method_val =
            alloc_slot_object(&mut proxy, &mut roots, reflect_map_val, &[])
                .value();
        roots.push(reflect_method_val);

        let new_object_map = add_constant_slot(
            &mut proxy,
            &mut roots,
            object_map_val,
            map_map_val,
            reflect_name,
            reflect_method_val,
        );
        roots.push(new_object_map);
        object_map_val = new_object_map;

        let ctype_build_struct_code = Value::from_i64(ctype_build_struct_idx);
        let ctype_build_struct_map_val = alloc_map(
            &mut proxy,
            &mut roots,
            map_map_val,
            ctype_build_struct_code,
            MapFlags::HAS_CODE.with(MapFlags::PRIMITIVE),
            &[],
            0,
        )
        .value();
        roots.push(ctype_build_struct_map_val);

        let ctype_build_struct_method_val = alloc_slot_object(
            &mut proxy,
            &mut roots,
            ctype_build_struct_map_val,
            &[],
        )
        .value();
        roots.push(ctype_build_struct_method_val);

        let new_object_map = add_constant_slot(
            &mut proxy,
            &mut roots,
            object_map_val,
            map_map_val,
            ctype_build_struct_name,
            ctype_build_struct_method_val,
        );
        roots.push(new_object_map);
        object_map_val = new_object_map;

        let ctype_field_info_at_code = Value::from_i64(ctype_field_info_at_idx);
        let ctype_field_info_at_map_val = alloc_map(
            &mut proxy,
            &mut roots,
            map_map_val,
            ctype_field_info_at_code,
            MapFlags::HAS_CODE.with(MapFlags::PRIMITIVE),
            &[],
            0,
        )
        .value();
        roots.push(ctype_field_info_at_map_val);

        let ctype_field_info_at_method_val = alloc_slot_object(
            &mut proxy,
            &mut roots,
            ctype_field_info_at_map_val,
            &[],
        )
        .value();
        roots.push(ctype_field_info_at_method_val);

        let new_object_map = add_constant_slot(
            &mut proxy,
            &mut roots,
            object_map_val,
            map_map_val,
            ctype_field_info_at_name,
            ctype_field_info_at_method_val,
        );
        roots.push(new_object_map);
        object_map_val = new_object_map;

        let ctype_scalar_tag_code = Value::from_i64(ctype_scalar_tag_idx);
        let ctype_scalar_tag_map_val = alloc_map(
            &mut proxy,
            &mut roots,
            map_map_val,
            ctype_scalar_tag_code,
            MapFlags::HAS_CODE.with(MapFlags::PRIMITIVE),
            &[],
            0,
        )
        .value();
        roots.push(ctype_scalar_tag_map_val);

        let ctype_scalar_tag_method_val = alloc_slot_object(
            &mut proxy,
            &mut roots,
            ctype_scalar_tag_map_val,
            &[],
        )
        .value();
        roots.push(ctype_scalar_tag_method_val);

        let new_object_map = add_constant_slot(
            &mut proxy,
            &mut roots,
            object_map_val,
            map_map_val,
            ctype_scalar_tag_name,
            ctype_scalar_tag_method_val,
        );
        roots.push(new_object_map);
        object_map_val = new_object_map;

        let obj_ptr = object_val.ref_bits() as *mut object::SlotObject;
        (*obj_ptr).map = object_map_val;

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

        let vm_eval_code = Value::from_i64(vm_eval_idx);
        let vm_eval_map_val = alloc_map(
            &mut proxy,
            &mut roots,
            map_map_val,
            vm_eval_code,
            MapFlags::HAS_CODE.with(MapFlags::PRIMITIVE),
            &[],
            0,
        )
        .value();
        roots.push(vm_eval_map_val);

        let vm_eval_method_val =
            alloc_slot_object(&mut proxy, &mut roots, vm_eval_map_val, &[])
                .value();
        roots.push(vm_eval_method_val);

        let mut vm_map_val = add_constant_slot(
            &mut proxy,
            &mut roots,
            object_map_val,
            map_map_val,
            vm_eval_name,
            vm_eval_method_val,
        );
        roots.push(vm_map_val);

        let vm_module_open_code = Value::from_i64(vm_module_open_idx);
        let vm_module_open_map_val = alloc_map(
            &mut proxy,
            &mut roots,
            map_map_val,
            vm_module_open_code,
            MapFlags::HAS_CODE.with(MapFlags::PRIMITIVE),
            &[],
            0,
        )
        .value();
        roots.push(vm_module_open_map_val);
        let vm_module_open_method_val = alloc_slot_object(
            &mut proxy,
            &mut roots,
            vm_module_open_map_val,
            &[],
        )
        .value();
        roots.push(vm_module_open_method_val);
        vm_map_val = add_constant_slot(
            &mut proxy,
            &mut roots,
            vm_map_val,
            map_map_val,
            vm_module_open_name,
            vm_module_open_method_val,
        );
        roots.push(vm_map_val);

        let vm_module_use_code = Value::from_i64(vm_module_use_idx);
        let vm_module_use_map_val = alloc_map(
            &mut proxy,
            &mut roots,
            map_map_val,
            vm_module_use_code,
            MapFlags::HAS_CODE.with(MapFlags::PRIMITIVE),
            &[],
            0,
        )
        .value();
        roots.push(vm_module_use_map_val);
        let vm_module_use_method_val = alloc_slot_object(
            &mut proxy,
            &mut roots,
            vm_module_use_map_val,
            &[],
        )
        .value();
        roots.push(vm_module_use_method_val);
        vm_map_val = add_constant_slot(
            &mut proxy,
            &mut roots,
            vm_map_val,
            map_map_val,
            vm_module_use_name,
            vm_module_use_method_val,
        );
        roots.push(vm_map_val);

        let vm_module_use_as_code = Value::from_i64(vm_module_use_as_idx);
        let vm_module_use_as_map_val = alloc_map(
            &mut proxy,
            &mut roots,
            map_map_val,
            vm_module_use_as_code,
            MapFlags::HAS_CODE.with(MapFlags::PRIMITIVE),
            &[],
            0,
        )
        .value();
        roots.push(vm_module_use_as_map_val);
        let vm_module_use_as_method_val = alloc_slot_object(
            &mut proxy,
            &mut roots,
            vm_module_use_as_map_val,
            &[],
        )
        .value();
        roots.push(vm_module_use_as_method_val);
        vm_map_val = add_constant_slot(
            &mut proxy,
            &mut roots,
            vm_map_val,
            map_map_val,
            vm_module_use_as_name,
            vm_module_use_as_method_val,
        );
        roots.push(vm_map_val);

        let vm_module_export_code = Value::from_i64(vm_module_export_idx);
        let vm_module_export_map_val = alloc_map(
            &mut proxy,
            &mut roots,
            map_map_val,
            vm_module_export_code,
            MapFlags::HAS_CODE.with(MapFlags::PRIMITIVE),
            &[],
            0,
        )
        .value();
        roots.push(vm_module_export_map_val);
        let vm_module_export_method_val = alloc_slot_object(
            &mut proxy,
            &mut roots,
            vm_module_export_map_val,
            &[],
        )
        .value();
        roots.push(vm_module_export_method_val);
        vm_map_val = add_constant_slot(
            &mut proxy,
            &mut roots,
            vm_map_val,
            map_map_val,
            vm_module_export_name,
            vm_module_export_method_val,
        );
        roots.push(vm_map_val);

        let vm_module_at_code = Value::from_i64(vm_module_at_idx);
        let vm_module_at_map_val = alloc_map(
            &mut proxy,
            &mut roots,
            map_map_val,
            vm_module_at_code,
            MapFlags::HAS_CODE.with(MapFlags::PRIMITIVE),
            &[],
            0,
        )
        .value();
        roots.push(vm_module_at_map_val);
        let vm_module_at_method_val = alloc_slot_object(
            &mut proxy,
            &mut roots,
            vm_module_at_map_val,
            &[],
        )
        .value();
        roots.push(vm_module_at_method_val);
        vm_map_val = add_constant_slot(
            &mut proxy,
            &mut roots,
            vm_map_val,
            map_map_val,
            vm_module_at_name,
            vm_module_at_method_val,
        );
        roots.push(vm_map_val);

        let vm_current_module_code = Value::from_i64(vm_current_module_idx);
        let vm_current_module_map_val = alloc_map(
            &mut proxy,
            &mut roots,
            map_map_val,
            vm_current_module_code,
            MapFlags::HAS_CODE.with(MapFlags::PRIMITIVE),
            &[],
            0,
        )
        .value();
        roots.push(vm_current_module_map_val);
        let vm_current_module_method_val = alloc_slot_object(
            &mut proxy,
            &mut roots,
            vm_current_module_map_val,
            &[],
        )
        .value();
        roots.push(vm_current_module_method_val);
        vm_map_val = add_constant_slot(
            &mut proxy,
            &mut roots,
            vm_map_val,
            map_map_val,
            vm_current_module_name,
            vm_current_module_method_val,
        );
        roots.push(vm_map_val);

        let vm_val =
            alloc_slot_object(&mut proxy, &mut roots, vm_map_val, &[]).value();
        roots.push(vm_val);

        let vm_name =
            intern_bootstrap(&mut proxy, &mut roots, &mut intern_table, "VM");
        add_dictionary_entry(
            &mut proxy,
            &mut roots,
            map_map_val,
            assoc_map_val,
            dictionary_val,
            vm_name,
            vm_val,
        );

        let reflectee_name = intern_bootstrap(
            &mut proxy,
            &mut roots,
            &mut intern_table,
            "reflectee",
        );
        let reflectee_set_name = intern_bootstrap(
            &mut proxy,
            &mut roots,
            &mut intern_table,
            "reflectee:",
        );
        let reflectee_offset = Value::from_i64(16);
        let reflectee_slots = [
            Slot::new(
                SlotFlags::ENUMERABLE.with(SlotFlags::ASSIGNABLE),
                reflectee_name,
                reflectee_offset,
            ),
            Slot::new(
                SlotFlags::ENUMERABLE.with(SlotFlags::ASSIGNMENT),
                reflectee_set_name,
                reflectee_offset,
            ),
        ];

        let mut mirror_map_val = alloc_map(
            &mut proxy,
            &mut roots,
            map_map_val,
            NONE_PLACEHOLDER,
            MapFlags::NONE,
            &reflectee_slots,
            1,
        )
        .value();
        roots.push(mirror_map_val);

        let mirror_val = alloc_slot_object(
            &mut proxy,
            &mut roots,
            mirror_map_val,
            &[none_val],
        )
        .value();
        roots.push(mirror_val);

        let mirror_primitives = [
            ("mirror_slot_count", "_MirrorSlotCount"),
            ("mirror_slot_name_at", "_MirrorSlotNameAt:"),
            ("mirror_at", "_MirrorAt:"),
            ("mirror_at_put", "_MirrorAt:Put:"),
            ("mirror_is_parent_at", "_MirrorIsParentAt:"),
            ("mirror_is_assignable_at", "_MirrorIsAssignableAt:"),
            ("mirror_add_slot_value", "_MirrorAddSlot:Value:"),
            ("mirror_remove_slot", "_MirrorRemoveSlot:"),
        ];

        for (prim_name, slot_name) in mirror_primitives {
            let prim_idx =
                primitives::primitive_index_by_name(&primitives, prim_name)
                    .expect("mirror primitive missing") as i64;
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

            let new_mirror_map = add_constant_slot(
                &mut proxy,
                &mut roots,
                mirror_map_val,
                map_map_val,
                slot_value,
                method_obj_val,
            );
            roots.push(new_mirror_map);
            mirror_map_val = new_mirror_map;
            let mirror_obj_ptr =
                mirror_val.ref_bits() as *mut object::SlotObject;
            (*mirror_obj_ptr).map = mirror_map_val;
        }

        let mirror_name = intern_bootstrap(
            &mut proxy,
            &mut roots,
            &mut intern_table,
            "Mirror",
        );
        add_dictionary_entry(
            &mut proxy,
            &mut roots,
            map_map_val,
            assoc_map_val,
            dictionary_val,
            mirror_name,
            mirror_val,
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
            intern_bootstrap(&mut proxy, &mut roots, &mut intern_table, "True");
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
            "False",
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
            intern_bootstrap(&mut proxy, &mut roots, &mut intern_table, "None");
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
            symbol_traits_map_val,
            ratio_traits_map_val,
            fixnum_traits_map_val,
            code_traits_map_val,
            float_traits_map_val,
            block_traits_map_val,
            object_map_val,
            new_object_map,
            vm_map_val,
            mirror_map_val,
            assoc_map_val,
            dictionary_map_val,
        ] {
            let map = &mut *(map_val.ref_bits() as *mut object::Map);
            if map.code.raw() == NONE_PLACEHOLDER.raw() {
                map.code = none_val;
            }
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
            symbol_traits: symbol_traits_val,
            ratio_traits: ratio_traits_val,
            fixnum_traits: fixnum_traits_val,
            code_traits: code_traits_val,
            float_traits: float_traits_val,
            mirror: mirror_val,
        };

        let mut vm = VM {
            heap_proxy: proxy,
            special,
            intern_table,
            primitives,
            assoc_map: assoc_map_val,
            ffi_cif_cache: HashMap::new(),
            dictionary: dictionary_val,
            current_module: None,
            modules: HashMap::new(),
            #[cfg(debug_assertions)]
            trace_assoc_name: None,
            #[cfg(debug_assertions)]
            trace_send_name: None,
        };
        vm.seed_user_module_from_dictionary();
        vm
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
        assert!(vm.special.symbol_traits.is_ref());
        assert!(vm.special.ratio_traits.is_ref());
        assert!(vm.special.fixnum_traits.is_ref());
        assert!(vm.special.code_traits.is_ref());
        assert!(vm.special.float_traits.is_ref());
        assert!(vm.special.mirror.is_ref());

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
