use crate::header::{Header, ObjectType};
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
        let ptr = (self as *const Self as *const u8).add(byte_offset as usize)
            as *const Value;
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
        let ptr = (self as *mut Self as *mut u8).add(byte_offset as usize)
            as *mut Value;
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

/// Initialize an array header at a raw allocation.
///
/// # Safety
///
/// `ptr` must point to at least `size_of::<Array>() + length * 8` bytes.
pub unsafe fn init_array(ptr: *mut Array, length: u64) {
    ptr.write(Array {
        header: Header::new(ObjectType::Array),
        length,
    });
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

/// Initialize a byte array header at a raw allocation.
///
/// # Safety
///
/// `ptr` must point to at least `size_of::<ByteArray>() + length` bytes.
pub unsafe fn init_byte_array(ptr: *mut ByteArray, length: u64) {
    ptr.write(ByteArray {
        header: Header::new(ObjectType::ByteArray),
        length,
    });
}

/// A compiled code object (bytecode + constant pool + source map).
///
/// ```text
/// [Header 8B] [constant_count: u32] [register_count: u16] [arg_count: u16]
/// [bytecode_len: u32] [temp_count: u16] [source_map_len: u16]
/// [feedback: Value 8B]
/// [constant_0: Value 8B] [constant_1: Value 8B] ...
/// [bytecode byte_0] [bytecode byte_1] ...
/// [source_map byte_0] [source_map byte_1] ...
/// ```
///
/// Code objects have no map pointer. The constant pool immediately follows
/// the fixed fields, then the raw bytecode bytes, then the source map bytes.
#[repr(C)]
pub struct Code {
    pub header: Header,
    constant_count: u32,
    register_count: u16,
    arg_count: u16,
    bytecode_len: u32,
    temp_count: u16,
    source_map_len: u16,
    pub feedback: Value,
}

const _: () = assert!(size_of::<Code>() == 32);

impl Code {
    #[inline(always)]
    pub fn constant_count(&self) -> u32 {
        self.constant_count
    }

    #[inline(always)]
    pub fn register_count(&self) -> u16 {
        self.register_count
    }

    #[inline(always)]
    pub fn arg_count(&self) -> u16 {
        self.arg_count
    }

    #[inline(always)]
    pub fn bytecode_len(&self) -> u32 {
        self.bytecode_len
    }

    #[inline(always)]
    pub fn temp_count(&self) -> u16 {
        self.temp_count
    }

    #[inline(always)]
    pub fn source_map_len(&self) -> u16 {
        self.source_map_len
    }

    /// Pointer to the first constant in the inline constant pool.
    #[inline(always)]
    fn constants_ptr(&self) -> *const Value {
        unsafe { (self as *const Code).add(1) as *const Value }
    }

    /// Access the inline constant pool.
    ///
    /// # Safety
    ///
    /// The memory after this `Code` must contain `constant_count` valid
    /// [`Value`] entries followed by `bytecode_len` bytes.
    #[inline(always)]
    pub unsafe fn constants(&self) -> &[Value] {
        core::slice::from_raw_parts(
            self.constants_ptr(),
            self.constant_count as usize,
        )
    }

    /// Access a single constant by index.
    ///
    /// # Safety
    ///
    /// `index` must be `< constant_count` and the inline memory must be valid.
    #[inline(always)]
    pub unsafe fn constant(&self, index: u32) -> Value {
        debug_assert!(index < self.constant_count);
        *self.constants_ptr().add(index as usize)
    }

    /// Pointer to the first bytecode byte (after the constant pool).
    #[inline(always)]
    fn bytecode_ptr(&self) -> *const u8 {
        unsafe {
            self.constants_ptr().add(self.constant_count as usize) as *const u8
        }
    }

    /// Access the raw bytecode bytes.
    ///
    /// # Safety
    ///
    /// The memory must be properly laid out (constants then bytecode).
    #[inline(always)]
    pub unsafe fn bytecode(&self) -> &[u8] {
        core::slice::from_raw_parts(
            self.bytecode_ptr(),
            self.bytecode_len as usize,
        )
    }

    /// Access the source map bytes (after bytecode).
    ///
    /// # Safety
    ///
    /// The memory must be properly laid out (constants, bytecode, source map).
    #[inline(always)]
    pub unsafe fn source_map(&self) -> &[u8] {
        let ptr = self.bytecode_ptr().add(self.bytecode_len as usize);
        core::slice::from_raw_parts(ptr, self.source_map_len as usize)
    }

    /// Total allocation size for this code object.
    #[inline(always)]
    pub fn byte_size(&self) -> usize {
        code_allocation_size(
            self.constant_count,
            self.bytecode_len,
            self.source_map_len as u32,
        )
    }
}

/// Compute the total allocation size for a [`Code`] object.
pub const fn code_allocation_size(
    constant_count: u32,
    bytecode_len: u32,
    source_map_len: u32,
) -> usize {
    size_of::<Code>()
        + constant_count as usize * size_of::<Value>()
        + bytecode_len as usize
        + source_map_len as usize
}

/// Initialize a code object at a raw allocation.
///
/// # Safety
///
/// `ptr` must point to at least
/// `code_allocation_size(constant_count, bytecode_len, source_map_len)`
/// bytes of writable memory. The caller must then write the constants,
/// bytecode, and source map into the inline areas.
pub unsafe fn init_code(
    ptr: *mut Code,
    constant_count: u32,
    register_count: u16,
    arg_count: u16,
    bytecode_len: u32,
    temp_count: u16,
    source_map_len: u16,
    feedback: Value,
) {
    ptr.write(Code {
        header: Header::new(ObjectType::Code),
        constant_count,
        register_count,
        arg_count,
        bytecode_len,
        temp_count,
        source_map_len,
        feedback,
    });
}

// ── Block ──────────────────────────────────────────────────────────

/// A block (closure) capturing its enclosing environment.
///
/// ```text
/// [Header 8B] [map: Value 8B] [env: Value 8B] [self: Value 8B]
/// ```
///
/// A block points to a [`Map`](crate::Map) whose `code` field holds the
/// compiled [`Code`] for this block. The map also describes any captured
/// variable slots.
#[repr(C)]
pub struct Block {
    pub header: Header,
    /// Tagged reference to this block's [`Map`](crate::Map).
    pub map: Value,
    /// Tagged reference to the captured environment (temp array) or None.
    pub env: Value,
    /// Tagged reference to the captured receiver (`self`).
    pub self_value: Value,
}

const _: () = assert!(size_of::<Block>() == 32);

// ── Primitive types (body TBD) ─────────────────────────────────────
//
// These have no map pointer. Lookups use the corresponding `_traits`
// entry in [`SpecialObjects`](crate::SpecialObjects).

/// Arbitrary-precision integer.
#[repr(C)]
pub struct BigNum {
    pub header: Header,
    pub sign: i8,
    _pad: [u8; 7],
    len: u64,
    data: [u64; 0],
}

const _: () = assert!(size_of::<BigNum>() == 24);

impl BigNum {
    pub const FIXNUM_MAX: i64 = (1_i64 << 62) - 1;

    pub fn init(&mut self, sign: i8, limbs: &[u64]) {
        self.header = Header::new(ObjectType::BigNum);
        let len = limbs.len();
        if len == 0 {
            self.sign = 0;
            self.len = 0;
            return;
        }

        self.sign = sign;
        self.len = len as u64;
        let dest = self.data.as_mut_ptr();
        unsafe { std::ptr::copy_nonoverlapping(limbs.as_ptr(), dest, len) };
    }

    pub fn init_zeroed(&mut self, sign: i8, len: usize) {
        self.header = Header::new(ObjectType::BigNum);
        if len == 0 {
            self.sign = 0;
            self.len = 0;
            return;
        }
        self.sign = sign;
        self.len = len as u64;
        let dest = self.data.as_mut_ptr();
        unsafe { std::ptr::write_bytes(dest, 0, len) };
    }

    #[inline(always)]
    pub fn len(&self) -> usize {
        self.len as usize
    }

    #[inline(always)]
    pub fn limbs(&self) -> &[u64] {
        let len = self.len();
        unsafe { std::slice::from_raw_parts(self.data.as_ptr(), len) }
    }

    #[inline(always)]
    pub fn limbs_mut(&mut self) -> &mut [u64] {
        let len = self.len();
        unsafe { std::slice::from_raw_parts_mut(self.data.as_mut_ptr(), len) }
    }

    pub fn to_fixnum_checked(&self) -> Option<i64> {
        let len = self.len();
        if len == 0 {
            return Some(0);
        }
        if len != 1 {
            return None;
        }
        let limb = self.limbs()[0];
        match self.sign {
            0 => Some(0),
            1 => {
                if limb <= Self::FIXNUM_MAX as u64 {
                    Some(limb as i64)
                } else {
                    None
                }
            }
            -1 => {
                let max_mag = 1_u64 << 62;
                if limb <= max_mag {
                    Some(-(limb as i64))
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    pub fn required_layout(len: usize) -> std::alloc::Layout {
        let base = std::alloc::Layout::new::<Self>();
        let limbs =
            std::alloc::Layout::array::<u64>(len).expect("create layout");
        let (layout, _) = base.extend(limbs).expect("extend layout");
        layout
    }
}

/// Foreign (FFI) pointer wrapper.
///
/// ```text
/// [Header 8B] [ptr: u64 8B] [size: u64 8B]
/// ```
///
/// `ptr` holds the raw C pointer as a `u64` (0 = null).
/// `size` holds the byte size of the region pointed to (0 = unknown/N/A).
///
/// Aliens have no map pointer. Lookups use
/// [`SpecialObjects::alien_traits`](crate::SpecialObjects::alien_traits).
/// The GC never evacuates Alien objects (`object_size` returns 0 for them).
#[repr(C)]
pub struct Alien {
    pub header: Header,
    pub ptr: u64,
    pub size: u64,
}

const _: () = assert!(size_of::<Alien>() == 24);

/// Allocation size for an [`Alien`] object.
pub const fn alien_allocation_size() -> usize {
    size_of::<Alien>()
}

/// Initialize an [`Alien`] at a raw allocation.
///
/// # Safety
///
/// `raw` must point to at least `alien_allocation_size()` (24) bytes of
/// writable memory.
pub unsafe fn init_alien(raw: *mut Alien, c_ptr: u64, size: u64) {
    raw.write(Alien {
        header: Header::new(ObjectType::Alien),
        ptr: c_ptr,
        size,
    });
}

/// Heap-allocated string — a length + pointer to a [`ByteArray`] backing
/// store.
///
/// ```text
/// [Header 8B] [length: u64 8B] [data: Value 8B]
/// ```
///
/// `length` is the number of content bytes (excludes the NUL terminator).
/// `data` is a tagged reference to a [`ByteArray`] whose bytes hold
/// valid UTF-8 followed by a `\0` terminator.
///
/// Strings have no map pointer. Lookups use
/// [`SpecialObjects::string_traits`](crate::SpecialObjects::string_traits).
#[repr(C)]
pub struct VMString {
    pub header: Header,
    length: u64,
    /// Tagged reference to the backing [`ByteArray`].
    pub data: Value,
}

const _: () = assert!(size_of::<VMString>() == 24);

impl VMString {
    /// Number of UTF-8 content bytes (excludes the NUL terminator).
    #[inline(always)]
    pub fn len(&self) -> u64 {
        self.length
    }

    #[inline(always)]
    pub fn is_empty(&self) -> bool {
        self.length == 0
    }

    /// Return the content bytes as a slice (excludes the NUL terminator).
    ///
    /// # Safety
    ///
    /// `self.data` must be a valid reference to a live [`ByteArray`] whose
    /// inline bytes are at least `len() + 1` long.
    #[inline(always)]
    pub unsafe fn as_bytes(&self) -> &[u8] {
        let ba: &ByteArray = self.data.as_ref();
        let all = ba.bytes();
        // Return only the content portion (without the NUL terminator).
        core::slice::from_raw_parts(all.as_ptr(), self.length as usize)
    }

    /// Return the content as a `&str`.
    ///
    /// # Safety
    ///
    /// `self.data` must be a valid reference to a live [`ByteArray`] and
    /// the content must be valid UTF-8.
    #[inline(always)]
    pub unsafe fn as_str(&self) -> &str {
        core::str::from_utf8_unchecked(self.as_bytes())
    }

    /// Pointer to the NUL-terminated byte sequence (C-string compatible).
    ///
    /// # Safety
    ///
    /// `self.data` must be a valid reference to a live [`ByteArray`].
    #[inline(always)]
    pub unsafe fn as_c_ptr(&self) -> *const u8 {
        let ba: &ByteArray = self.data.as_ref();
        ba.bytes().as_ptr()
    }
}

/// Initialize a string object at a raw allocation.
///
/// `data` is a tagged reference to a [`ByteArray`] that already contains
/// `length` bytes of valid UTF-8 followed by a `\0` terminator.
///
/// # Safety
///
/// `ptr` must point to at least `size_of::<VMString>()` (24) bytes of writable
/// memory. `data` must be a valid tagged reference to a live [`ByteArray`].
pub unsafe fn init_str(ptr: *mut VMString, length: u64, data: Value) {
    ptr.write(VMString {
        header: Header::new(ObjectType::Str),
        length,
        data,
    });
}

/// Heap-allocated symbol.
///
/// Symbols use the same in-memory layout as [`VMString`]: header + byte
/// length + backing [`ByteArray`] reference. The backing bytes are expected to
/// include a trailing NUL terminator while `length` stores content size.
pub type VMSymbol = VMString;

/// Initialize a symbol object at a raw allocation.
///
/// `data` must reference a [`ByteArray`] containing `length` content bytes
/// followed by a trailing `\0` byte.
///
/// # Safety
///
/// `ptr` must point to at least `size_of::<VMSymbol>()` writable bytes.
pub unsafe fn init_symbol(ptr: *mut VMSymbol, length: u64, data: Value) {
    ptr.write(VMSymbol {
        header: Header::new(ObjectType::Symbol),
        length,
        data,
    });
}

/// Exact rational number (numerator / denominator).
#[repr(C)]
pub struct Ratio {
    pub header: Header,
    pub numerator: Value,
    pub denominator: Value,
}

const _: () = assert!(size_of::<Ratio>() == 24);

pub unsafe fn init_ratio(
    ptr: *mut Ratio,
    numerator: Value,
    denominator: Value,
) {
    ptr.write(Ratio {
        header: Header::new(ObjectType::Ratio),
        numerator,
        denominator,
    });
}

// ── Float ─────────────────────────────────────────────────────────

/// A boxed IEEE 754 double-precision floating-point number.
///
/// ```text
/// [Header 8B] [value: f64 8B]
/// ```
///
/// Floats have no map pointer. Lookups use
/// [`SpecialObjects::float_traits`](crate::SpecialObjects::float_traits).
#[repr(C)]
pub struct Float {
    pub header: Header,
    pub value: f64,
}

const _: () = assert!(size_of::<Float>() == 16);

/// Initialize a float object at a raw allocation.
///
/// # Safety
///
/// `ptr` must point to at least `float_allocation_size()` (16) bytes of
/// writable memory.
pub unsafe fn init_float(ptr: *mut Float, value: f64) {
    ptr.write(Float {
        header: Header::new(ObjectType::Float),
        value,
    });
}

/// Allocation size for a [`Float`] object.
pub const fn float_allocation_size() -> usize {
    size_of::<Float>()
}
