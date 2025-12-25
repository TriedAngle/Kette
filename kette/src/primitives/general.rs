use std::collections::HashSet;

use crate::{
    Allocator, Array, ByteArray, ExecutionResult, Handle, ObjectType,
    PrimitiveContext, SlotDescriptor, SlotObject, SlotTags, Tagged, Value,
    primitives::inputs,
};

#[inline]
fn is_constant_slot(tags: SlotTags) -> bool {
    !tags.contains(SlotTags::ASSIGNABLE) && !tags.contains(SlotTags::ASSIGNMENT)
}

#[inline]
fn name_key(name: Tagged<ByteArray>) -> usize {
    name.as_ptr() as usize
}

/// ( target traits -- target )
pub fn add_trait_slots(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let [traits_v, target_v] = inputs(ctx);

    // SAFETY: caller ensures these are slot objects
    let target = unsafe { target_v.cast::<SlotObject>() };
    // SAFETY: caller ensures these are slot objects
    let traits = unsafe { traits_v.cast::<SlotObject>() };

    // SAFETY: handles are valid
    let target_ptr = target.as_ptr();
    // SAFETY: handles are valid
    let traits_ptr = traits.as_ptr();

    // SAFETY: valid pointers
    let target_map_tagged = unsafe { (*target_ptr).map };
    // SAFETY: valid pointers
    let traits_map_tagged = unsafe { (*traits_ptr).map };

    // SAFETY: map pointers valid
    let target_map = unsafe { target_map_tagged.as_ref() };
    // SAFETY: map pointers valid
    let traits_map = unsafe { traits_map_tagged.as_ref() };

    // Start with all existing slots from target
    let mut new_slots: Vec<SlotDescriptor> = target_map.slots().to_vec();

    // Build set of existing names (to detect duplicates)
    let mut existing: HashSet<usize> = HashSet::with_capacity(new_slots.len());
    for sd in &new_slots {
        existing.insert(name_key(sd.name));
    }

    // Add only constant slots from traits, rejecting duplicates
    for sd in traits_map.slots().iter().copied() {
        let tags = sd.tags();
        if !is_constant_slot(tags) {
            return ExecutionResult::Panic(
                "addTraitSlots: only constant slots can be used",
            );
        }

        let k = name_key(sd.name);
        if existing.contains(&k) {
            return ExecutionResult::Panic(
                "addTraitSlots: Duplicate slot name",
            );
        }
        existing.insert(k);
        new_slots.push(sd);
    }

    // Allocate new map and patch ONLY this object
    let new_map = ctx.heap.allocate_slots_map(
        &new_slots,
        target_map.code,
        target_map.effect,
    );

    // SAFETY: we have exclusive access; patch map pointer
    unsafe {
        (*target_ptr).map = new_map.into();
    }

    ExecutionResult::Normal
}

/// ( target traits -- target )
pub fn remove_trait_slots(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let [target_v, traits_v] = inputs(ctx);

    // SAFETY: caller ensures these are slot objects
    let target = unsafe { target_v.cast::<SlotObject>() };
    // SAFETY: caller ensures these are slot objects
    let traits = unsafe { traits_v.cast::<SlotObject>() };

    // SAFETY: handles are valid
    let target_ptr = target.as_ptr();
    let traits_ptr = traits.as_ptr();

    // SAFETY: valid pointers
    let target_map_tagged = unsafe { (*target_ptr).map };
    // SAFETY: valid pointers
    let traits_map_tagged = unsafe { (*traits_ptr).map };

    // SAFETY: map pointers valid
    let target_map = unsafe { target_map_tagged.as_ref() };
    // SAFETY: map pointers valid
    let traits_map = unsafe { traits_map_tagged.as_ref() };

    // Names to remove (only constant slots from traits)
    let mut remove: HashSet<usize> = HashSet::new();
    for sd in traits_map.slots().iter() {
        let tags = sd.tags();
        if is_constant_slot(tags) {
            remove.insert(name_key(sd.name));
        }
    }

    // Keep everything except constant slots whose names are in `remove`
    let mut new_slots: Vec<SlotDescriptor> =
        Vec::with_capacity(target_map.slot_count());
    for sd in target_map.slots().iter().copied() {
        let tags = sd.tags();
        if is_constant_slot(tags) && remove.contains(&name_key(sd.name)) {
            continue;
        }
        new_slots.push(sd);
    }

    // Allocate new map and patch ONLY this object
    let new_map = ctx.heap.allocate_slots_map(
        &new_slots,
        target_map.code,
        target_map.effect,
    );

    // SAFETY: we have exclusive access; patch map pointer
    unsafe {
        (*target_ptr).map = new_map.into();
    }

    ExecutionResult::Normal
}

pub fn identity(ctx: &mut PrimitiveContext) -> ExecutionResult {
    ctx.outputs[0] = ctx.receiver;
    ExecutionResult::Normal
}

/// ( obj -- new_obj )
pub fn clone_obj(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let [obj] = inputs(ctx);

    if !obj.is_object() {
        ctx.outputs[0] = obj;
        return ExecutionResult::Normal;
    }

    // SAFETY: checked
    let heap_obj = unsafe { obj.as_heap_value_handle() };

    let new_val: Handle<Value> = match heap_obj.header.object_type() {
        Some(ObjectType::Slot) => {
            // SAFETY: Type checked via header
            let slot_obj = unsafe { obj.cast::<SlotObject>() };
            // SAFETY: this is safe
            let map = unsafe { slot_obj.map.promote_to_handle() };
            let slots = slot_obj.inner().slots();

            let res = ctx.heap.allocate_slots(map, slots);
            res.into()
        }
        Some(ObjectType::Array) => {
            // SAFETY: Type checked via header
            let arr = unsafe { obj.cast::<Array>() };
            let data = arr.inner().fields();

            let res = ctx.heap.allocate_array(data);
            res.into()
        }
        Some(ObjectType::ByteArray) => {
            // SAFETY: Type checked via header
            let ba = unsafe { obj.cast::<ByteArray>() };
            let data = ba.as_bytes();

            // TODO: handle alignment
            let res = ctx.heap.allocate_aligned_bytearray(data, 8);
            // SAFETY: just allocated
            res.into()
        }
        // For other types (Method, Quotation, Float etc.) we typically return self
        // Falling back to identity for now.
        _ => obj,
    };

    ctx.outputs[0] = new_val;
    ExecutionResult::Normal
}

/// ( ... prototype -- new_obj )
/// Pops N values from the stack where N is the number of assignable slots in prototype.
/// TODO: implement this for some more than slots
pub fn clone_obj_boa(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let [obj] = inputs(ctx);

    // CloneBoa mainly makes sense for SlotObjects (objects with assignable slots).
    // If passed a primitive or non-slot object, we panic or return error.
    if !obj.is_object() {
        return ExecutionResult::Panic("cloneBoa: expected heap object");
    }

    // SAFETY: checked
    let heap_obj = unsafe { obj.as_heap_value_handle() };

    if heap_obj.header.object_type() != Some(ObjectType::Slot) {
        return ExecutionResult::Panic("cloneBoa: expected SlotObject");
    }

    // SAFETY: checked
    let prototype = unsafe { obj.cast::<SlotObject>() };

    // SAFETY: this is safe
    let map = unsafe { prototype.map.promote_to_handle() };

    let count = map.assignable_slots_count();

    // SAFETY: We assume the interpreter ensures stack depth before calling,
    // or pop_slice_unchecked handles bounds implicitly/unsafe.
    let slots_data = unsafe { ctx.state.stack_pop_slice_unchecked(count) };

    let new_obj = ctx.heap.allocate_slots(map, slots_data);

    // SAFETY: this is safe
    ctx.outputs[0] = new_obj.into();
    ExecutionResult::Normal
}
