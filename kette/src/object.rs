use std::ptr::NonNull;

use crate::{TaggedPtr, TaggedValue, Visitor};

#[repr(u8)]
#[derive(Debug, Copy, Clone)]
pub enum ValueTag {
    Integer = 0b0,
    Reference = 0b01,
    Header = 0b11,
}

#[repr(u8)]
#[derive(Debug, Copy, Clone)]
pub enum ObjectType {
    Slot = 0b0000,
    Map = 0b0001,
    Array = 0b0010,
    ByteArray = 0b0011,
    Max = 0b1111,
}

bitflags::bitflags! {
    pub struct HeaderFlags: u8 {
        const MARK = 1 << 0;
        const PIN = 1 << 1;
        const FORWARD = 1 << 2;
        const LARGE = 1 << 3;
    }
}

// [0..<2 tag]
// [2..<6 object]
// [8..<12 age]
// [12..<16 flags]
// [32..<64 additional data]
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
pub struct SlotObject {
    pub header: Header,
    pub map: TaggedPtr<Map>,
}

#[repr(C)]
#[derive(Copy, Clone)]
pub struct Map {
    header: Header,
}

#[repr(C)]
#[derive(Copy, Clone)]
pub struct Array {
    header: Header,
}

#[repr(C)]
#[derive(Copy, Clone)]
pub struct ByteArray {
    header: Header,
}

impl Header {
    pub const TAG_SHIFT: u64 = 0;
    pub const TAG_MASK: u64 = 0b11 << Self::TAG_SHIFT;

    pub const OBJ_SHIFT: u64 = 2;
    pub const OBJ_MASK: u64 = 0b1111 << Self::OBJ_SHIFT;

    pub const AGE_SHIFT: u64 = 8;
    pub const AGE_MASK: u64 = 0xF << Self::AGE_SHIFT;

    pub const FLAGS_SHIFT: u64 = 12;
    pub const FLAGS_MASK: u64 = 0xF << Self::FLAGS_SHIFT;

    pub const DATA_SHIFT: u64 = 32;
    pub const DATA_MASK: u64 = 0xFFFF_FFFFu64 << Self::DATA_SHIFT;

    #[inline]
    pub fn encode(ty: ObjectType, age: u8, flags: HeaderFlags, data: u32) -> Header {
        let inner = (ValueTag::Header as u64)
            | ((ty as u64) << Self::OBJ_SHIFT)
            | (((age as u64) & 0xF) << Self::AGE_SHIFT)
            | (((flags.bits() as u64) & 0xF) << Self::FLAGS_SHIFT)
            | ((data as u64) << Self::DATA_SHIFT);

        Header(inner)
    }

    #[inline]
    pub fn zeroed() -> Self {
        Self(0)
    }

    #[inline]
    pub fn object_type(self) -> ObjectType {
        match ((self.0 & Self::OBJ_MASK) >> Self::OBJ_SHIFT) as u8 {
            0b0000 => ObjectType::Slot,
            0b0001 => ObjectType::Map,
            0b0010 => ObjectType::Array,
            0b0011 => ObjectType::ByteArray,
            0b1111 => ObjectType::Max,
            _ => ObjectType::Max, // fallback to a sentinel
        }
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

    #[inline]
    pub fn set_object_type(&mut self, ty: ObjectType) -> &mut Self {
        self.0 = (self.0 & !Self::OBJ_MASK) | (((ty as u64) << Self::OBJ_SHIFT) & Self::OBJ_MASK);
        self
    }

    #[inline]
    pub fn set_age(&mut self, age: u8) -> &mut Self {
        let age_bits = ((age as u64) & 0xF) << Self::AGE_SHIFT;
        self.0 = (self.0 & !Self::AGE_MASK) | age_bits;
        self
    }

    #[inline]
    pub fn set_flags(&mut self, flags: HeaderFlags) -> &mut Self {
        let f = ((flags.bits() as u64) & 0xF) << Self::FLAGS_SHIFT;
        self.0 = (self.0 & !Self::FLAGS_MASK) | f;
        self
    }

    #[inline]
    pub fn set_data(&mut self, data: u32) -> &mut Self {
        let d = (data as u64) << Self::DATA_SHIFT;
        self.0 = (self.0 & !Self::DATA_MASK) | d;
        self
    }

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
}

impl SlotObject {
    pub fn init(me: *mut Self, map: NonNull<Map>) {
        unsafe { (*me).header = Header::encode(ObjectType::Slot, 0, HeaderFlags::empty(), 0) }
        unsafe { (*me).map = TaggedPtr::from_nonnull(map) }
    }

    pub fn visit(&mut self, visitor: &mut impl Visitor) {
        let map = unsafe { self.map.as_ref() };
        visitor.visit(self.map.into());
    }
}
