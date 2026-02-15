use std::alloc::Layout;
use std::ptr;

use heap::{HeapProxy, RootProvider};
use object::{
    code_allocation_size, float_allocation_size, init_array, init_byte_array,
    init_code, init_float, init_map, map_allocation_size,
    slot_object_allocation_size, Array, Block, ByteArray, Code, Float, Header,
    Map, ObjectType, Slot, SlotFlags, SlotObject, Tagged, Value,
};

/// Allocate a [`Map`] with inline slots.
///
/// # Safety
///
/// The caller must ensure `map_map` and `code` are valid tagged values,
/// and `slots` contains valid [`Slot`] entries.
pub unsafe fn alloc_map(
    proxy: &mut HeapProxy,
    roots: &mut dyn RootProvider,
    map_map: Value,
    code: Value,
    slots: &[Slot],
    value_count: u32,
) -> Tagged<Map> {
    let slot_count = slots.len() as u32;
    let size = map_allocation_size(slot_count);
    let layout = Layout::from_size_align(size, 8).unwrap();
    let ptr = proxy.allocate(layout, roots);

    let map_ptr = ptr.as_ptr() as *mut Map;
    init_map(map_ptr, map_map, code, slot_count, value_count);

    if !slots.is_empty() {
        let slots_dst = map_ptr.add(1) as *mut Slot;
        ptr::copy_nonoverlapping(slots.as_ptr(), slots_dst, slots.len());
    }

    Tagged::from_value(Value::from_ptr(map_ptr))
}

/// Allocate a [`SlotObject`] with inline values.
///
/// # Safety
///
/// `map` must be a valid tagged reference to a [`Map`], and `values`
/// must match the map's `value_count`.
pub unsafe fn alloc_slot_object(
    proxy: &mut HeapProxy,
    roots: &mut dyn RootProvider,
    map: Value,
    values: &[Value],
) -> Tagged<SlotObject> {
    let count = values.len() as u32;
    let size = slot_object_allocation_size(count);
    let layout = Layout::from_size_align(size, 8).unwrap();
    let ptr = proxy.allocate(layout, roots);

    let obj_ptr = ptr.as_ptr() as *mut SlotObject;
    ptr::write(
        obj_ptr,
        SlotObject {
            header: Header::new(ObjectType::Slots),
            map,
        },
    );

    if !values.is_empty() {
        let vals_dst = obj_ptr.add(1) as *mut Value;
        ptr::copy_nonoverlapping(values.as_ptr(), vals_dst, values.len());
    }

    Tagged::from_value(Value::from_ptr(obj_ptr))
}

/// Allocate an [`Array`] with the given elements.
///
/// # Safety
///
/// All elements must be valid [`Value`]s.
pub unsafe fn alloc_array(
    proxy: &mut HeapProxy,
    roots: &mut dyn RootProvider,
    elements: &[Value],
) -> Tagged<Array> {
    let len = elements.len();
    let size = size_of::<Array>() + len * size_of::<Value>();
    let layout = Layout::from_size_align(size, 8).unwrap();
    let ptr = proxy.allocate(layout, roots);

    let arr_ptr = ptr.as_ptr() as *mut Array;
    init_array(arr_ptr, len as u64);

    if !elements.is_empty() {
        let elems_dst = arr_ptr.add(1) as *mut Value;
        ptr::copy_nonoverlapping(elements.as_ptr(), elems_dst, len);
    }

    Tagged::from_value(Value::from_ptr(arr_ptr))
}

/// Allocate a [`ByteArray`] with the given bytes.
pub unsafe fn alloc_byte_array(
    proxy: &mut HeapProxy,
    roots: &mut dyn RootProvider,
    bytes: &[u8],
) -> Tagged<ByteArray> {
    let len = bytes.len();
    let size = size_of::<ByteArray>() + len;
    let layout = Layout::from_size_align(size, 8).unwrap();
    let ptr = proxy.allocate(layout, roots);

    let ba_ptr = ptr.as_ptr() as *mut ByteArray;
    init_byte_array(ba_ptr, len as u64);

    if !bytes.is_empty() {
        let bytes_dst = ba_ptr.add(1) as *mut u8;
        ptr::copy_nonoverlapping(bytes.as_ptr(), bytes_dst, len);
    }

    Tagged::from_value(Value::from_ptr(ba_ptr))
}

/// Allocate a [`Code`] object with inline constants and bytecode.
///
/// # Safety
///
/// `constants` must contain valid [`Value`]s.
pub unsafe fn alloc_code(
    proxy: &mut HeapProxy,
    roots: &mut dyn RootProvider,
    constants: &[Value],
    bytecode: &[u8],
    register_count: u16,
    arg_count: u16,
    temp_count: u16,
) -> Tagged<Code> {
    let constant_count = constants.len() as u32;
    let bytecode_len = bytecode.len() as u32;
    let size = code_allocation_size(constant_count, bytecode_len);
    let layout = Layout::from_size_align(size, 8).unwrap();
    let ptr = proxy.allocate(layout, roots);

    let code_ptr = ptr.as_ptr() as *mut Code;
    init_code(
        code_ptr,
        constant_count,
        register_count,
        arg_count,
        bytecode_len,
        temp_count,
    );

    if !constants.is_empty() {
        let consts_dst = code_ptr.add(1) as *mut Value;
        ptr::copy_nonoverlapping(
            constants.as_ptr(),
            consts_dst,
            constants.len(),
        );
    }

    if !bytecode.is_empty() {
        let bc_dst =
            (code_ptr.add(1) as *mut Value).add(constants.len()) as *mut u8;
        ptr::copy_nonoverlapping(bytecode.as_ptr(), bc_dst, bytecode.len());
    }

    Tagged::from_value(Value::from_ptr(code_ptr))
}

/// Allocate a [`Block`] (closure).
///
/// # Safety
///
/// `map` must be a valid tagged reference to a [`Map`].
pub unsafe fn alloc_block(
    proxy: &mut HeapProxy,
    roots: &mut dyn RootProvider,
    map: Value,
) -> Tagged<Block> {
    let size = size_of::<Block>();
    let layout = Layout::from_size_align(size, 8).unwrap();
    let ptr = proxy.allocate(layout, roots);

    let block_ptr = ptr.as_ptr() as *mut Block;
    ptr::write(
        block_ptr,
        Block {
            header: Header::new(ObjectType::Block),
            map,
        },
    );

    Tagged::from_value(Value::from_ptr(block_ptr))
}

/// Allocate a [`Float`] object.
///
/// # Safety
///
/// Caller must ensure all rooted values are valid.
pub unsafe fn alloc_float(
    proxy: &mut HeapProxy,
    roots: &mut dyn RootProvider,
    value: f64,
) -> Tagged<Float> {
    let size = float_allocation_size();
    let layout = Layout::from_size_align(size, 8).unwrap();
    let ptr = proxy.allocate(layout, roots);

    let float_ptr = ptr.as_ptr() as *mut Float;
    init_float(float_ptr, value);

    Tagged::from_value(Value::from_ptr(float_ptr))
}

/// Create a new Map that is `old_map` plus one additional CONSTANT slot.
///
/// Returns the new Map value. The caller must update the object's `.map`
/// field to point to the new map.
///
/// # Safety
///
/// `old_map` must be a valid tagged reference to a [`Map`]. `map_map`,
/// `name`, and `value` must be valid tagged values. All values must be
/// rooted before calling.
pub unsafe fn add_constant_slot(
    proxy: &mut HeapProxy,
    roots: &mut dyn RootProvider,
    old_map: Value,
    map_map: Value,
    name: Value,
    value: Value,
) -> Value {
    let old: &Map = old_map.as_ref();
    let old_slot_count = old.slot_count();
    let old_value_count = old.value_count();
    let old_code = old.code;
    let old_slots = old.slots();

    // Build new slot array: old slots + new constant slot
    let new_slot_count = old_slot_count + 1;
    let mut slots = Vec::with_capacity(new_slot_count as usize);
    for s in old_slots {
        slots.push(*s);
    }
    slots.push(Slot::new(SlotFlags::CONSTANT, name, value));

    let size = map_allocation_size(new_slot_count);
    let layout = Layout::from_size_align(size, 8).unwrap();
    let ptr = proxy.allocate(layout, roots);

    let map_ptr = ptr.as_ptr() as *mut Map;
    init_map(map_ptr, map_map, old_code, new_slot_count, old_value_count);

    let slots_dst = map_ptr.add(1) as *mut Slot;
    ptr::copy_nonoverlapping(slots.as_ptr(), slots_dst, slots.len());

    Value::from_ptr(map_ptr)
}

/// Create a new Map that is `old_map` minus the CONSTANT slot at `slot_index`.
///
/// Returns the new Map value.
///
/// # Safety
///
/// `old_map` must be a valid tagged reference to a [`Map`] with
/// `slot_index < slot_count`. All values must be rooted before calling.
pub unsafe fn remove_constant_slot(
    proxy: &mut HeapProxy,
    roots: &mut dyn RootProvider,
    old_map: Value,
    map_map: Value,
    slot_index: u32,
) -> Value {
    let old: &Map = old_map.as_ref();
    let old_slot_count = old.slot_count();
    let old_value_count = old.value_count();
    let old_code = old.code;
    let old_slots = old.slots();

    debug_assert!(slot_index < old_slot_count);

    let new_slot_count = old_slot_count - 1;
    let mut slots = Vec::with_capacity(new_slot_count as usize);
    for (i, s) in old_slots.iter().enumerate() {
        if i as u32 != slot_index {
            slots.push(*s);
        }
    }

    let size = map_allocation_size(new_slot_count);
    let layout = Layout::from_size_align(size, 8).unwrap();
    let ptr = proxy.allocate(layout, roots);

    let map_ptr = ptr.as_ptr() as *mut Map;
    init_map(map_ptr, map_map, old_code, new_slot_count, old_value_count);

    if !slots.is_empty() {
        let slots_dst = map_ptr.add(1) as *mut Slot;
        ptr::copy_nonoverlapping(slots.as_ptr(), slots_dst, slots.len());
    }

    Value::from_ptr(map_ptr)
}
