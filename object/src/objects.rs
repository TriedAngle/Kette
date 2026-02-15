use crate::header::Header;
use crate::Value;

// ── SlotObject ─────────────────────────────────────────────────────

/// A regular object with a hidden map and inline assignable-slot values.
///
/// ```text
/// [Header 8B] [map: Value 8B] [value_0 8B] [value_1 8B] ...
/// ```
///
/// The number of inline values is determined by the [`Map`](crate::Map)
/// this object points to.
#[repr(C)]
pub struct SlotObject {
    pub header: Header,
    /// Tagged reference to this object's [`Map`](crate::Map).
    pub map: Value,
}

const _: () = assert!(size_of::<SlotObject>() == 16);

impl SlotObject {
    /// Read a tagged value at `byte_offset` from the start of this object.
    ///
    /// # Safety
    ///
    /// `byte_offset` must point to a valid [`Value`] within this object's
    /// allocated memory.
    #[inline(always)]
    pub unsafe fn read_value(&self, byte_offset: u32) -> Value {
        let ptr = (self as *const Self as *const u8).add(byte_offset as usize) as *const Value;
        ptr.read()
    }

    /// Write a tagged value at `byte_offset` from the start of this object.
    ///
    /// # Safety
    ///
    /// `byte_offset` must point to a valid [`Value`] within this object's
    /// allocated memory.
    #[inline(always)]
    pub unsafe fn write_value(&mut self, byte_offset: u32, value: Value) {
        let ptr = (self as *mut Self as *mut u8).add(byte_offset as usize) as *mut Value;
        ptr.write(value);
    }

    /// Byte offset of the first inline value (right after `header` + `map`).
    pub const VALUES_OFFSET: u32 = size_of::<SlotObject>() as u32;
}

/// Compute the total allocation size for a [`SlotObject`] with `value_count`
/// inline values.
pub const fn slot_object_allocation_size(value_count: u32) -> usize {
    size_of::<SlotObject>() + value_count as usize * size_of::<Value>()
}

// ── Array ──────────────────────────────────────────────────────────

/// A variable-length array of tagged [`Value`]s.
///
/// ```text
/// [Header 8B] [length: u64 8B] [elem_0 8B] [elem_1 8B] ...
/// ```
///
/// Arrays have no map pointer. Lookups use
/// [`SpecialObjects::array_traits`](crate::SpecialObjects::array_traits).
#[repr(C)]
pub struct Array {
    pub header: Header,
    length: u64,
}

const _: () = assert!(size_of::<Array>() == 16);

impl Array {
    #[inline(always)]
    pub fn len(&self) -> u64 {
        self.length
    }

    #[inline(always)]
    pub fn is_empty(&self) -> bool {
        self.length == 0
    }

    /// # Safety
    ///
    /// The inline memory after this struct must contain `len()` valid elements.
    #[inline(always)]
    pub unsafe fn elements(&self) -> &[Value] {
        let ptr = (self as *const Array).add(1) as *const Value;
        core::slice::from_raw_parts(ptr, self.length as usize)
    }

    /// # Safety
    ///
    /// `index < len()` and the inline memory must be valid.
    #[inline(always)]
    pub unsafe fn element(&self, index: u64) -> Value {
        debug_assert!(index < self.length);
        let ptr = (self as *const Array).add(1) as *const Value;
        *ptr.add(index as usize)
    }
}

// ── ByteArray ──────────────────────────────────────────────────────

/// A variable-length byte buffer.
///
/// ```text
/// [Header 8B] [length: u64 8B] [byte_0] [byte_1] ...
/// ```
///
/// ByteArrays have no map pointer. Lookups use
/// [`SpecialObjects::bytearray_traits`](crate::SpecialObjects::bytearray_traits).
#[repr(C)]
pub struct ByteArray {
    pub header: Header,
    length: u64,
}

const _: () = assert!(size_of::<ByteArray>() == 16);

impl ByteArray {
    #[inline(always)]
    pub fn len(&self) -> u64 {
        self.length
    }

    #[inline(always)]
    pub fn is_empty(&self) -> bool {
        self.length == 0
    }

    /// # Safety
    ///
    /// The inline memory after this struct must contain `len()` valid bytes.
    #[inline(always)]
    pub unsafe fn bytes(&self) -> &[u8] {
        let ptr = (self as *const ByteArray).add(1) as *const u8;
        core::slice::from_raw_parts(ptr, self.length as usize)
    }
}

// ── Code ───────────────────────────────────────────────────────────

/// A compiled code object (bytecode + constant pool).
///
/// Body TBD — only the header exists for now.
#[repr(C)]
pub struct Code {
    pub header: Header,
}

// ── Block ──────────────────────────────────────────────────────────

/// A block (closure) capturing its enclosing environment.
///
/// Body TBD — only the header exists for now.
#[repr(C)]
pub struct Block {
    pub header: Header,
}

// ── Primitive types (body TBD) ─────────────────────────────────────
//
// These have no map pointer. Lookups use the corresponding `_traits`
// entry in [`SpecialObjects`](crate::SpecialObjects).

/// Arbitrary-precision integer.
#[repr(C)]
pub struct BigNum {
    pub header: Header,
}

/// Foreign (FFI) pointer wrapper.
#[repr(C)]
pub struct Alien {
    pub header: Header,
}

/// Heap-allocated string.
#[repr(C)]
pub struct Str {
    pub header: Header,
}

/// Exact rational number (numerator / denominator).
#[repr(C)]
pub struct Ratio {
    pub header: Header,
}
