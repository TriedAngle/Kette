use crate::header::{Header, ObjectType};
use crate::slot::Slot;
use crate::Value;

/// A hidden map (shape descriptor) for prototypical objects.
///
/// Layout in memory:
/// ```text
/// [Header 8B] [map: Value 8B] [code: Value 8B] [slot_count: u32 4B] [_pad 4B]
/// [Slot_0 24B] [Slot_1 24B] ... [Slot_N-1 24B]
/// ```
///
/// The inline slots immediately follow the fixed fields. The `map` field
/// points to `special_objects.map_map`.
#[repr(C)]
pub struct Map {
    pub header: Header,
    /// Tagged reference to this map's own map (→ `map_map`).
    pub map: Value,
    /// Nil or tagged reference to a [`Code`](crate::Code) object.
    pub code: Value,
    slot_count: u32,
    value_count: u32,
}

const _: () = assert!(size_of::<Map>() == 32);

impl Map {
    #[inline(always)]
    pub fn slot_count(&self) -> u32 {
        self.slot_count
    }

    #[inline(always)]
    pub fn value_count(&self) -> u32 {
        self.value_count
    }

    /// Byte size of the entire map including inline slots.
    #[inline(always)]
    pub fn byte_size(&self) -> usize {
        size_of::<Map>() + self.slot_count as usize * size_of::<Slot>()
    }

    /// Pointer to the first inline slot.
    #[inline(always)]
    fn slots_ptr(&self) -> *const Slot {
        unsafe { (self as *const Map).add(1) as *const Slot }
    }

    /// Access the inline slot array.
    ///
    /// # Safety
    ///
    /// The memory after this `Map` must contain `slot_count` valid [`Slot`]
    /// entries.
    #[inline(always)]
    pub unsafe fn slots(&self) -> &[Slot] {
        core::slice::from_raw_parts(self.slots_ptr(), self.slot_count as usize)
    }

    /// Access a single inline slot by index.
    ///
    /// # Safety
    ///
    /// `index` must be `< slot_count` and the inline memory must be valid.
    #[inline(always)]
    pub unsafe fn slot(&self, index: u32) -> &Slot {
        debug_assert!(index < self.slot_count);
        &*self.slots_ptr().add(index as usize)
    }
}

impl core::fmt::Debug for Map {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Map")
            .field("header", &self.header)
            .field("map", &self.map)
            .field("code", &self.code)
            .field("slot_count", &self.slot_count)
            .field("value_count", &self.value_count)
            .finish()
    }
}

/// Compute the total allocation size for a [`Map`] with `slot_count` inline
/// slots.
pub const fn map_allocation_size(slot_count: u32) -> usize {
    size_of::<Map>() + slot_count as usize * size_of::<Slot>()
}

/// Initialize a map header at a raw allocation.
///
/// # Safety
///
/// `ptr` must point to at least `map_allocation_size(slot_count)` bytes of
/// writable memory.
pub unsafe fn init_map(
    ptr: *mut Map,
    map_map: Value,
    code: Value,
    slot_count: u32,
    value_count: u32,
) {
    ptr.write(Map {
        header: Header::new(ObjectType::Map),
        map: map_map,
        code,
        slot_count,
        value_count,
    });
}
