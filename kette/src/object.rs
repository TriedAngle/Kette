use std::ptr::NonNull;

use crate::{TaggedPtr, TaggedU64, TaggedUsize, TaggedValue};

#[repr(u8)]
#[derive(Debug, Copy, Clone)]
pub enum ValueTag {
    Integer = 0b00,
    Reference = 0b01,
    Header = 0b11,
}

#[repr(u8)]
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum ObjectKind {
    Object = 0,
    Map = 1,
}

#[repr(u8)]
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum ObjectType {
    Slot = 0b00000,
    Array = 0b00010,
    ByteArray = 0b00011,
    Max = 0b11111,
}

/// What kind of map this is. Lives in the unified 5-bit TYPE field
/// when `kind == Kind::Map`.
#[repr(u8)]
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum MapType {
    Slot = 0,
    Array = 1,
}

bitflags::bitflags! {
    pub struct HeaderFlags: u8 {
        const MARK    = 1 << 0;
        const PIN     = 1 << 1;
        const FORWARD = 1 << 2;
        const LARGE   = 1 << 3;
    }
}

// Bit layout:
//
// [0..<2  tag]            2 bits  (ValueTag)
// [2..<3  kind]           1 bit   (0 = Object, 1 = Map)
// [3..<8  type]           5 bits  (ObjectType or MapType depending on kind)
// [8..<12 age]            4 bits
// [12..<16 flags]         4 bits
// [16..<32 reserved]     16 bits  (unused; keep zeroed for now)
// [32..<64 data]         32 bits  (general-purpose payload)
#[repr(C)]
#[derive(Copy, Clone)]
pub struct Header(u64);

#[repr(C)]
#[derive(Copy, Clone)]
pub struct Object {
    pub header: Header,
}

#[repr(C)]
#[derive(Copy, Clone)]
pub struct Map {
    pub header: Header,
}

#[repr(C)]
#[derive(Copy, Clone)]
pub struct SlotMap {
    pub map: Map,
    pub assignable_slots: TaggedU64,
}

#[repr(C)]
#[derive(Copy, Clone)]
pub struct ArrayMap {
    pub map: Map,
    size: TaggedUsize,
}

#[repr(C)]
#[derive(Copy, Clone)]
pub struct SlotObject {
    pub header: Header,
    pub map: TaggedPtr<SlotMap>,
    pub slots: [TaggedValue; 0],
}

#[repr(C)]
#[derive(Copy, Clone)]
pub struct Array {
    pub header: Header,
    pub map: TaggedPtr<ArrayMap>,
    pub fields: [TaggedValue; 0],
}

#[repr(C)]
#[derive(Copy, Clone)]
pub struct ByteArray {
    pub header: Header,
    pub data: [u8; 0],
}

impl Header {
    pub const TAG_SHIFT: u64 = 0;
    pub const TAG_MASK: u64 = 0b11 << Self::TAG_SHIFT;

    pub const KIND_SHIFT: u64 = 2;
    pub const KIND_MASK: u64 = 0b1 << Self::KIND_SHIFT;

    pub const TYPE_SHIFT: u64 = 3;
    pub const TYPE_MASK: u64 = 0b1_1111 << Self::TYPE_SHIFT; // 5 bits

    pub const AGE_SHIFT: u64 = 8;
    pub const AGE_MASK: u64 = 0xF << Self::AGE_SHIFT;

    pub const FLAGS_SHIFT: u64 = 12;
    pub const FLAGS_MASK: u64 = 0xF << Self::FLAGS_SHIFT;

    // [16..32) reserved for future use (keep zero)

    /// Additional data lives in bits [32..64)
    pub const DATA_SHIFT: u64 = 32;
    pub const DATA_MASK: u64 = 0xFFFF_FFFFu64 << Self::DATA_SHIFT;

    // ---- Suggested sub-layout inside DATA ----
    const DATA_LO16_MASK: u32 = 0xFFFF; // cached size/slots

    #[inline]
    pub fn zeroed() -> Self {
        Self(0)
    }

    // Unified low-level encode that takes the raw 5-bit type.
    #[inline]
    fn encode_raw(
        kind: ObjectKind,
        type_bits: u8,
        age: u8,
        flags: HeaderFlags,
        data: u32,
    ) -> Header {
        let inner = (ValueTag::Header as u64)
            | (((kind as u64) & 0x1) << Self::KIND_SHIFT)
            | ((((type_bits as u64) & 0x1F) << Self::TYPE_SHIFT) & Self::TYPE_MASK)
            | (((age as u64) & 0xF) << Self::AGE_SHIFT)
            | (((flags.bits() as u64) & 0xF) << Self::FLAGS_SHIFT)
            | ((data as u64) << Self::DATA_SHIFT);
        Header(inner)
    }

    /// Encode an Object header.
    #[inline]
    pub fn encode_object(ty: ObjectType, age: u8, flags: HeaderFlags, data: u32) -> Header {
        Self::encode_raw(ObjectKind::Object, ty as u8, age, flags, data)
    }

    /// Encode a Map header.
    #[inline]
    pub fn encode_map(ty: MapType, age: u8, flags: HeaderFlags, data: u32) -> Header {
        Self::encode_raw(ObjectKind::Map, ty as u8, age, flags, data)
    }

    #[inline]
    pub fn is_forwarded(&self) -> bool {
        self.flags().contains(HeaderFlags::FORWARD)
    }

    #[inline]
    pub unsafe fn forwarding_slot_ptr<T>(&self) -> *mut *mut T {
        let self_ptr = (self as *const Header as *mut Header).cast::<u8>();
        unsafe { self_ptr.add(size_of::<Header>()) as *mut *mut T }
    }

    #[inline]
    pub unsafe fn set_forwarding_to<T>(&mut self, new_ptr: NonNull<T>) {
        self.0 |= (HeaderFlags::FORWARD.bits() as u64) << Header::FLAGS_SHIFT;
        let slot = unsafe { self.forwarding_slot_ptr::<T>() };
        unsafe { slot.write(new_ptr.as_ptr()) };
    }

    #[inline]
    pub unsafe fn get_forwarded<T>(&self) -> NonNull<T> {
        let slot = unsafe { self.forwarding_slot_ptr::<T>() };
        unsafe { NonNull::new_unchecked(slot.read()) }
    }

    // ---- getters ----
    #[inline]
    pub fn kind(self) -> ObjectKind {
        if ((self.0 & Self::KIND_MASK) >> Self::KIND_SHIFT) as u8 == 0 {
            ObjectKind::Object
        } else {
            ObjectKind::Map
        }
    }

    #[inline]
    pub fn type_bits(self) -> u8 {
        ((self.0 & Self::TYPE_MASK) >> Self::TYPE_SHIFT) as u8
    }

    /// Meaningful only when kind() == Kind::Object.
    #[inline]
    pub fn object_type(self) -> Option<ObjectType> {
        if self.kind() != ObjectKind::Object {
            return None;
        }
        Some(match self.type_bits() {
            0b00000 => ObjectType::Slot,
            0b00010 => ObjectType::Array,
            0b00011 => ObjectType::ByteArray,
            0b11111 => ObjectType::Max,
            _ => ObjectType::Max,
        })
    }

    /// Meaningful only when kind() == Kind::Map.
    #[inline]
    pub fn map_type(self) -> Option<MapType> {
        if self.kind() != ObjectKind::Map {
            return None;
        }
        Some(match self.type_bits() {
            0 => MapType::Slot,
            1 => MapType::Array,
            _ => return None,
        })
    }

    #[inline]
    pub fn age(self) -> u8 {
        ((self.0 & Self::AGE_MASK) >> Self::AGE_SHIFT) as u8
    }

    #[inline]
    pub fn flags(self) -> HeaderFlags {
        HeaderFlags::from_bits_truncate(((self.0 & Self::FLAGS_MASK) >> Self::FLAGS_SHIFT) as u8)
    }

    #[inline]
    pub fn data(self) -> u32 {
        ((self.0 & Self::DATA_MASK) >> Self::DATA_SHIFT) as u32
    }

    // ---- setters ----
    #[inline]
    pub fn set_kind(&mut self, kind: ObjectKind) -> &mut Self {
        self.0 = (self.0 & !Self::KIND_MASK) | (((kind as u64) & 0x1) << Self::KIND_SHIFT);
        self
    }

    #[inline]
    pub fn set_object_type(&mut self, ty: ObjectType) -> &mut Self {
        self.set_kind(ObjectKind::Object);
        self.0 = (self.0 & !Self::TYPE_MASK)
            | ((((ty as u64) & 0x1F) << Self::TYPE_SHIFT) & Self::TYPE_MASK);
        self
    }

    #[inline]
    pub fn set_map_type(&mut self, ty: MapType) -> &mut Self {
        self.set_kind(ObjectKind::Map);
        self.0 = (self.0 & !Self::TYPE_MASK)
            | ((((ty as u64) & 0x1F) << Self::TYPE_SHIFT) & Self::TYPE_MASK);
        self
    }

    #[inline]
    pub fn set_age(&mut self, age: u8) -> &mut Self {
        self.0 = (self.0 & !Self::AGE_MASK) | (((age as u64) & 0xF) << Self::AGE_SHIFT);
        self
    }

    #[inline]
    pub fn set_flags(&mut self, flags: HeaderFlags) -> &mut Self {
        self.0 =
            (self.0 & !Self::FLAGS_MASK) | (((flags.bits() as u64) & 0xF) << Self::FLAGS_SHIFT);
        self
    }

    #[inline]
    pub fn set_data(&mut self, data: u32) -> &mut Self {
        self.0 = (self.0 & !Self::DATA_MASK) | ((data as u64) << Self::DATA_SHIFT);
        self
    }

    // ---- convenience bits ----
    #[inline]
    pub fn is_marked(self) -> bool {
        self.flags().contains(HeaderFlags::MARK)
    }

    #[inline]
    pub fn mark(&mut self) -> &mut Self {
        self.0 |= (HeaderFlags::MARK.bits() as u64) << Self::FLAGS_SHIFT;
        self
    }

    #[inline]
    pub fn unmark(&mut self) -> &mut Self {
        self.0 &= !((HeaderFlags::MARK.bits() as u64) << Self::FLAGS_SHIFT);
        self
    }

    // ---- DATA helpers ----
    /// Extracts the cached 16-bit value from DATA (used by SlotObject/Array for small sizes).
    #[inline]
    pub fn data_lo16(self) -> u16 {
        (self.data() & Self::DATA_LO16_MASK) as u16
    }

    /// Puts a 16-bit cache into DATA’s low 16 bits (does not touch the rest of DATA).
    #[inline]
    pub fn set_data_lo16(&mut self, lo16: u16) -> &mut Self {
        let mut data = self.data();
        data &= !Self::DATA_LO16_MASK;
        data |= lo16 as u32;
        self.set_data(data)
    }
}

impl Map {
    #[inline]
    pub fn init_with_type(&mut self, mt: MapType) {
        self.header = Header::encode_map(mt, 0, HeaderFlags::empty(), 0);
    }

    #[inline]
    pub fn map_type(&self) -> Option<MapType> {
        self.header.map_type()
    }
}

impl SlotMap {
    #[inline]
    pub fn new(assignable_slots: TaggedU64) -> Self {
        let mut m = Map {
            header: Header::zeroed(),
        };
        m.init_with_type(MapType::Slot);
        Self {
            map: m,
            assignable_slots,
        }
    }

    #[inline]
    pub fn assignable_slots_count(&self) -> usize {
        u64::from(self.assignable_slots) as usize
    }
}

impl ArrayMap {
    #[inline]
    pub fn new(size: TaggedUsize) -> Self {
        let mut m = Map {
            header: Header::zeroed(),
        };
        m.init_with_type(MapType::Array);
        Self { map: m, size }
    }

    #[inline]
    pub fn size(&self) -> usize {
        usize::from(self.size)
    }
}

impl SlotObject {
    pub fn init(mut me: NonNull<Self>, map: NonNull<SlotMap>) {
        let map_ref = unsafe { map.as_ref() };
        let slots = map_ref.assignable_slots_count();

        let cache16 = if slots > u16::MAX as usize {
            0xFFFF
        } else {
            slots as u16
        };

        let me = unsafe { me.as_mut() };
        me.header = Header::encode_object(ObjectType::Slot, 0, HeaderFlags::empty(), 0);
        me.header.set_data_lo16(cache16);
        me.map = TaggedPtr::from_nonnull(map);
    }

    #[inline]
    fn slots_ptr(&self) -> *const TaggedValue {
        self.slots.as_ptr()
    }

    #[inline]
    fn slots_mut_ptr(&mut self) -> *mut TaggedValue {
        self.slots.as_mut_ptr()
    }

    #[inline]
    pub fn slots(&self) -> &[TaggedValue] {
        let len = self.assignable_slots();
        unsafe { std::slice::from_raw_parts(self.slots_ptr(), len) }
    }

    /// Borrow all slots as a mutable slice (checked).
    #[inline]
    pub fn slots_mut(&mut self) -> &mut [TaggedValue] {
        let len = self.assignable_slots();
        unsafe { std::slice::from_raw_parts_mut(self.slots_mut_ptr(), len) }
    }

    #[inline]
    pub fn assignable_slots(&self) -> usize {
        let cached16 = self.header.data_lo16();

        if cached16 != u16::MAX {
            cached16 as usize
        } else {
            let map = unsafe { self.map.as_ref() };
            map.assignable_slots_count()
        }
    }

    #[inline]
    pub fn get_slot(&self, index: usize) -> Option<TaggedValue> {
        if index < self.assignable_slots() {
            Some(unsafe { self.slots_ptr().add(index).read() })
        } else {
            None
        }
    }

    #[inline]
    pub fn set_slot(&mut self, index: usize, value: TaggedValue) -> bool {
        if index < self.assignable_slots() {
            unsafe { self.slots_mut_ptr().add(index).write(value) };
            true
        } else {
            false
        }
    }

    /// Caller must ensure `index < assignable_slots()`.
    #[inline]
    pub unsafe fn get_slot_unchecked(&self, index: usize) -> TaggedValue {
        unsafe { self.slots_ptr().add(index).read() }
    }

    /// Caller must ensure `index < assignable_slots()`.
    #[inline]
    pub unsafe fn set_slot_unchecked(&mut self, index: usize, value: TaggedValue) {
        unsafe { self.slots_mut_ptr().add(index).write(value) };
    }
}

// ---------------------- Array ----------------------

impl Array {
    /// Initialize an Array with `map`. Caches size (u16) in header DATA[0..16].
    pub fn init(mut me: NonNull<Self>, map: NonNull<ArrayMap>) {
        let map_ref = unsafe { map.as_ref() };
        let size = map_ref.size();

        let cache16 = if size > u16::MAX as usize {
            0xFFFF
        } else {
            size as u16
        };

        let me = unsafe { me.as_mut() };
        me.header = Header::encode_object(ObjectType::Array, 0, HeaderFlags::empty(), 0);
        me.header.set_data_lo16(cache16);
        me.map = TaggedPtr::from_nonnull(map);
    }

    #[inline]
    fn fields_ptr(&self) -> *const TaggedValue {
        self.fields.as_ptr()
    }

    #[inline]
    fn fields_mut_ptr(&mut self) -> *mut TaggedValue {
        self.fields.as_mut_ptr()
    }

    /// Length of the array. Uses cached 16-bit size if available, otherwise reads the map.
    #[inline]
    pub fn len(&self) -> usize {
        let cached = self.header.data_lo16();
        if cached != u16::MAX {
            cached as usize
        } else {
            let map = unsafe { self.map.as_ref() };
            map.size()
        }
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    #[inline]
    pub fn fields(&self) -> &[TaggedValue] {
        let len = self.len();
        unsafe { std::slice::from_raw_parts(self.fields_ptr(), len) }
    }

    #[inline]
    pub fn fields_mut(&mut self) -> &mut [TaggedValue] {
        let len = self.len();
        unsafe { std::slice::from_raw_parts_mut(self.fields_mut_ptr(), len) }
    }

    #[inline]
    pub fn get(&self, index: usize) -> Option<TaggedValue> {
        if index < self.len() {
            Some(unsafe { self.fields_ptr().add(index).read() })
        } else {
            None
        }
    }

    #[inline]
    pub fn set(&mut self, index: usize, value: TaggedValue) -> bool {
        if index < self.len() {
            unsafe { self.fields_mut_ptr().add(index).write(value) };
            true
        } else {
            false
        }
    }

    /// Caller must ensure `index < len()`.
    #[inline]
    pub unsafe fn get_unchecked(&self, index: usize) -> TaggedValue {
        unsafe { self.fields_ptr().add(index).read() }
    }

    /// Caller must ensure `index < len()`.
    #[inline]
    pub unsafe fn set_unchecked(&mut self, index: usize, value: TaggedValue) {
        unsafe { self.fields_mut_ptr().add(index).write(value) };
    }
}
