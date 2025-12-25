use std::{
    mem,
    sync::atomic::{AtomicU8, Ordering},
};

pub mod activation;
pub mod arrays;
pub mod bytearrays;
pub mod executable;
pub mod floats;
pub mod message;
pub mod parser;
pub mod quotations;
pub mod slots;
pub mod threads;

use crate::{
    ActivationObject, Array, ByteArray, Float, LookupResult, Message,
    Quotation, Selector, SlotMap, SlotObject, ThreadObject, Value, ValueTag,
    Visitable, VisitedLink, Visitor,
};

#[repr(u8)]
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum ObjectKind {
    Object = 0,
    Map = 1,
}

#[rustfmt::skip]
#[repr(u8)]
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum ObjectType {
    Slot        = 0b00000,
    Array       = 0b00010,
    ByteArray   = 0b00011,
    Activation  = 0b00100,
    Quotation   = 0b00111,
    Message     = 0b01000,
    Float       = 0b01001,
    BigNum      = 0b01010,
    Thread      = 0b01011,
    Max         = 0b11111,
}

/// What kind of map this is. Lives in the unified 5-bit TYPE field
/// when `kind == Kind::Map`.
#[repr(u8)]
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum MapType {
    Slot = 0b000,
    Max = 0b11111,
}

bitflags::bitflags! {
    /// Header flags are intentionally tiny (currently only PINNED).
    #[repr(transparent)]
    #[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
    pub struct HeaderFlags: u8 {
        const PINNED = 1 << 0;
    }
}

#[repr(C)]
#[derive(Debug)]
pub struct Header {
    /// Bits:
    /// [0..2) tag  (ValueTag: Number=0b00, Ref=0b01, Header=0b11)
    /// [2]    kind (0=Object, 1=Map)
    /// [3..8) type (5 bits: ObjectType or MapType)
    pub ty: u8,

    pub flags: HeaderFlags,
    /// GC mark byte.
    pub mark: AtomicU8,
    /// Padding / future use.
    pub _reserved: u8,
    /// General payload (formerly bits [32..64) of the packed header).
    pub data: u32,
}

pub trait Object: Sized + Visitable {
    fn lookup(
        &self,
        selector: Selector,
        link: Option<&VisitedLink>,
    ) -> LookupResult {
        // SAFETY: must be valid here
        let s = selector.name.as_utf8().expect("get string");
        unimplemented!(
            "lookup with: {s} and {link:?} on type that is not lookupable"
        );
    }
}

pub trait PtrSizedObject: Object {
    fn to_ptr_sized(self) -> u64;
    fn from_ptr_sized(value: u64) -> Self;
}

pub trait HeapObject: Object {
    const KIND: ObjectKind;
    const TYPE_BITS: u8;

    fn header(&self) -> &Header {
        // SAFETY: every heap object has header
        unsafe { mem::transmute::<&Self, &Header>(self) }
    }
    fn header_mut(&mut self) -> &mut Header {
        // SAFETY: every heap object has header
        unsafe { mem::transmute::<&mut Self, &mut Header>(self) }
    }

    fn heap_size(&self) -> usize;
}

#[repr(C)]
#[derive(Debug)]
pub struct HeapValue {
    pub header: Header,
}

#[repr(C)]
#[derive(Debug)]
pub struct Map {
    pub header: Header,
}

impl Header {
    pub const FLAG_PINNED: u8 = 1 << 0;

    pub const TAG_SHIFT: u8 = 0;
    pub const TAG_MASK: u8 = 0b11;

    pub const KIND_SHIFT: u8 = 2;
    pub const KIND_MASK: u8 = 0b1 << Self::KIND_SHIFT;

    pub const TYPE_SHIFT: u8 = 3;
    pub const TYPE_MASK: u8 = 0b1_1111 << Self::TYPE_SHIFT;

    pub const TAG_HEADER_BITS: u8 = 0b11;

    /// Equivalent of your old `HEADER_FREE` (0b11111011).
    /// This corresponds to: tag=Header(0b11), kind=Object(0), type=Max(0b11111).
    pub const TY_FREE: u8 = ((ValueTag::Header as u8) & Self::TAG_MASK)
        | (((ObjectKind::Object as u8) & 0x1) << Self::KIND_SHIFT)
        | (((ObjectType::Max as u8) & 0x1F) << Self::TYPE_SHIFT);

    #[inline]
    pub const fn new_object(ty: ObjectType) -> Self {
        Self::new_raw(ObjectKind::Object, ty as u8, HeaderFlags::empty(), 0)
    }

    #[inline]
    pub const fn new_map(ty: MapType) -> Self {
        Self::new_raw(ObjectKind::Map, ty as u8, HeaderFlags::empty(), 0)
    }

    #[inline]
    pub const fn new_object2(
        ty: ObjectType,
        flags: HeaderFlags,
        data: u32,
    ) -> Self {
        Self::new_raw(ObjectKind::Object, ty as u8, flags, data)
    }

    #[inline]
    pub const fn new_map2(ty: MapType, flags: HeaderFlags, data: u32) -> Self {
        Self::new_raw(ObjectKind::Map, ty as u8, flags, data)
    }

    #[inline]
    const fn new_raw(
        kind: ObjectKind,
        type_bits: u8,
        flags: HeaderFlags,
        data: u32,
    ) -> Self {
        let ty = (Self::TAG_HEADER_BITS & Self::TAG_MASK)
            | (((kind as u8) & 0x1) << Self::KIND_SHIFT)
            | (((type_bits & 0x1F) << Self::TYPE_SHIFT) & Self::TYPE_MASK);

        Header {
            ty,
            flags,
            mark: AtomicU8::new(0),
            _reserved: 0,
            data,
        }
    }

    #[inline]
    pub fn tag(&self) -> ValueTag {
        match self.ty & Self::TAG_MASK {
            0b00 => ValueTag::Fixnum,
            0b01 => ValueTag::Reference,
            0b11 => ValueTag::Header,
            _ => unreachable!("2-bit tag only"),
        }
    }

    #[inline]
    pub fn kind(&self) -> ObjectKind {
        if (self.ty & Self::KIND_MASK) == 0 {
            ObjectKind::Object
        } else {
            ObjectKind::Map
        }
    }

    #[inline]
    pub fn type_bits(&self) -> u8 {
        (self.ty & Self::TYPE_MASK) >> Self::TYPE_SHIFT
    }

    #[inline]
    pub fn object_type(&self) -> Option<ObjectType> {
        if self.kind() != ObjectKind::Object {
            return None;
        }
        Some(match self.type_bits() {
            0b00000 => ObjectType::Slot,
            0b00010 => ObjectType::Array,
            0b00011 => ObjectType::ByteArray,
            0b00100 => ObjectType::Activation,
            0b00111 => ObjectType::Quotation,
            0b01000 => ObjectType::Message,
            0b01001 => ObjectType::Float,
            0b01010 => ObjectType::BigNum,
            0b11111 => ObjectType::Max,
            _ => unreachable!("object type doesn't exist"),
        })
    }

    #[inline]
    pub fn map_type(&self) -> Option<MapType> {
        if self.kind() != ObjectKind::Map {
            return None;
        }
        Some(match self.type_bits() {
            0b000 => MapType::Slot,
            _ => unreachable!("map type doesn't exist"),
        })
    }

    #[inline]
    pub fn is_free(&self) -> bool {
        self.ty == Self::TY_FREE
    }

    #[inline]
    pub fn new_free(size_bytes: u32) -> Self {
        Header {
            ty: Self::TY_FREE,
            flags: HeaderFlags::empty(),
            mark: AtomicU8::new(0),
            _reserved: 0,
            data: size_bytes,
        }
    }

    #[inline]
    pub fn is_pinned(&self) -> bool {
        self.flags.contains(HeaderFlags::PINNED)
    }

    #[inline]
    pub fn set_pinned(&mut self, pinned: bool) {
        self.flags.set(HeaderFlags::PINNED, pinned);
    }

    #[inline]
    pub fn is_marked(&self) -> bool {
        self.mark.load(Ordering::Relaxed) != 0
    }

    #[inline]
    pub fn mark(&self) {
        self.mark.store(1, Ordering::Relaxed);
    }

    #[inline]
    pub fn unmark(&self) {
        self.mark.store(0, Ordering::Relaxed);
    }

    #[inline]
    pub fn data(&self) -> u32 {
        self.data
    }

    #[inline]
    pub fn set_data(&mut self, data: u32) {
        self.data = data;
    }
}

impl Map {
    #[inline]
    pub fn init(&mut self, ty: MapType) {
        self.header = Header::new_map(ty);
    }

    #[inline]
    pub fn map_type(&self) -> Option<MapType> {
        self.header.map_type()
    }

    #[inline(always)]
    fn is<T: HeapObject>(&self) -> bool {
        self.header.kind() == ObjectKind::Map
            && self.header.type_bits() == T::TYPE_BITS
    }

    #[inline(always)]
    pub fn downcast_ref_match<T: HeapObject>(&self) -> &T {
        if self.is::<T>() {
            // SAFETY: already matched in call site
            unsafe { &*(self as *const Map as *const T) }
        } else {
            // SAFETY: already matched in call site
            unsafe { std::hint::unreachable_unchecked() }
        }
    }

    #[inline(always)]
    pub fn downcast_mut_match<T: HeapObject>(&mut self) -> &mut T {
        if self.is::<T>() {
            // SAFETY: already matched in call site
            unsafe { &mut *(self as *mut Map as *mut T) }
        } else {
            // SAFETY: already matched in call site
            unsafe { std::hint::unreachable_unchecked() }
        }
    }
}

impl HeapValue {
    #[inline(always)]
    pub fn is<T: HeapObject>(&self) -> bool {
        self.header.kind() == T::KIND && self.header.type_bits() == T::TYPE_BITS
    }

    #[inline(always)]
    pub fn downcast_ref<T: HeapObject>(&self) -> Option<&T> {
        if self.is::<T>() {
            // SAFETY: guarded by tag check + layout invariant of HeapObject
            Some(unsafe { &*(self as *const HeapValue as *const T) })
        } else {
            None
        }
    }

    #[inline(always)]
    pub fn downcast_mut<T: HeapObject>(&mut self) -> Option<&mut T> {
        if self.is::<T>() {
            // SAFETY: guarded by tag check + layout invariant ofHeapObject
            Some(unsafe { &mut *(self as *mut HeapValue as *mut T) })
        } else {
            None
        }
    }

    /// Fast path for when already matched on type.
    /// # Safety
    /// must be be correct invariant
    #[inline(always)]
    pub unsafe fn downcast_ref_unchecked<T: HeapObject>(&self) -> &T {
        debug_assert!(self.is::<T>());
        // SAFETY: caller proves via match / debug_assert
        unsafe { &*(self as *const HeapValue as *const T) }
    }

    /// Fast path for when already matched on type.
    /// # Safety
    /// must be be correct invariant
    #[inline(always)]
    pub fn downcast_mut_unchecked<T: HeapObject>(&mut self) -> &mut T {
        debug_assert!(self.is::<T>());
        // SAFETY: caller proves via match / debug_assert
        unsafe { &mut *(self as *mut HeapValue as *mut T) }
    }

    /// Helper to downcast
    /// must be checked
    #[inline(always)]
    pub fn downcast_ref_match<T: HeapObject>(&self) -> &T {
        if self.is::<T>() {
            // SAFETY: already matched in call site
            unsafe { &*(self as *const HeapValue as *const T) }
        } else {
            // SAFETY: already matched in call site
            unsafe { std::hint::unreachable_unchecked() }
        }
    }

    /// Helper to downcast
    /// must be checked
    #[inline(always)]
    pub fn downcast_mut_match<T: HeapObject>(&mut self) -> &mut T {
        if self.is::<T>() {
            // SAFETY: already matched in call site
            unsafe { &mut *(self as *mut HeapValue as *mut T) }
        } else {
            // SAFETY: already matched in call site
            unsafe { std::hint::unreachable_unchecked() }
        }
    }
}

impl Object for HeapValue {
    #[rustfmt::skip]
    fn lookup(&self, selector: Selector, link: Option<&VisitedLink>) -> LookupResult {
        // SAFETY: only objects will ever be looked up 
        match unsafe { self.header.object_type().unwrap_unchecked() } {
            ObjectType::Slot        => self.downcast_ref_match::<SlotObject>().lookup(selector, link),
            ObjectType::Array       => self.downcast_ref_match::<Array>().lookup(selector, link),
            ObjectType::ByteArray   => self.downcast_ref_match::<ByteArray>().lookup(selector, link),
            ObjectType::Activation  => self.downcast_ref_match::<ActivationObject>().lookup(selector, link),
            ObjectType::Quotation   => self.downcast_ref_match::<Quotation>().lookup(selector, link),
            ObjectType::Float       => self.downcast_ref_match::<Float>().lookup(selector, link),
            ObjectType::BigNum      => unimplemented!(),
            ObjectType::Thread      => unimplemented!(),
            ObjectType::Message | ObjectType::Max => {
                unreachable!("illegal object type for lookup")
            }
        }
    }
}
impl HeapObject for HeapValue {
    const KIND: ObjectKind = ObjectKind::Object;
    const TYPE_BITS: u8 = ObjectType::Max as u8;

    #[rustfmt::skip]
    fn heap_size(&self) -> usize {
        match self.header.kind() {
            ObjectKind::Object => {
                // SAFETY: matched to this 
                match unsafe { self.header.object_type().unwrap_unchecked() } {
                    ObjectType::Slot       => self.downcast_ref_match::<SlotObject>().heap_size(),
                    ObjectType::Array      => self.downcast_ref_match::<Array>().heap_size(),
                    ObjectType::ByteArray  => self.downcast_ref_match::<ByteArray>().heap_size(),
                    ObjectType::Activation => self.downcast_ref_match::<ActivationObject>().heap_size(),
                    ObjectType::Quotation  => self.downcast_ref_match::<Quotation>().heap_size(),
                    ObjectType::Message    => self.downcast_ref_match::<Message>().heap_size(),
                    ObjectType::Float      => self.downcast_ref_match::<Float>().heap_size(),
                    ObjectType::BigNum     => unimplemented!(),
                    ObjectType::Thread     => unimplemented!(),
                    ObjectType::Max        => unreachable!(),
                }
            }
            ObjectKind::Map => {
                // SAFETY: matched to this 
                match unsafe { self.header.map_type().unwrap_unchecked() } {
                    MapType::Slot      => self.downcast_ref_match::<SlotMap>().heap_size(),
                    MapType::Max => unreachable!(),
                }
            }
        }
    }
}

impl Visitable for Value {}
impl Object for Value {
    fn lookup(
        &self,
        selector: Selector,
        link: Option<&VisitedLink>,
    ) -> LookupResult {
        if let Some(_num) = self.as_tagged_fixnum::<i64>() {
            let traits = selector.vm.specials.fixnum_traits;
            return traits.lookup(selector, link);
        }

        // Safety: if its not a fixnum it must be a heap object
        let object = unsafe { self.as_heap_handle_unchecked() };
        object.lookup(selector, link)
    }
}

// Idea:
// visiting an object means we visit only its direct nodes.
// so when we call on a generic object, we dispatch here on the actual object types.
// the actual object types will then call visitor.visit() on its edges.
impl Visitable for HeapValue {
    #[rustfmt::skip]
    fn visit_edges_mut(&mut self, visitor: &mut impl Visitor) {
        match self.header.kind() {
            ObjectKind::Map => {
                // SAFETY: matched to this
                match unsafe { self.header.map_type().unwrap_unchecked() } {
                    MapType::Slot       => self.downcast_mut_match::<SlotMap>().visit_edges_mut(visitor),
                    MapType::Max        => unreachable!(),
                }
            }
            ObjectKind::Object => {
                // SAFETY: matched to this
                match unsafe { self.header.object_type().unwrap_unchecked() } {
                    ObjectType::Slot        => self.downcast_mut_match::<SlotObject>().visit_edges_mut(visitor),
                    ObjectType::Array       => self.downcast_mut_match::<Array>().visit_edges_mut(visitor),
                    ObjectType::Activation  => self.downcast_mut_match::<ActivationObject>().visit_edges_mut(visitor),
                    ObjectType::Quotation   => self.downcast_mut_match::<Quotation>().visit_edges_mut(visitor),
                    ObjectType::Message     => self.downcast_mut_match::<Message>().visit_edges_mut(visitor),
                    ObjectType::Thread      => self.downcast_mut_match::<ThreadObject>().visit_edges_mut(visitor),
                    ObjectType::ByteArray | ObjectType::Float | ObjectType::BigNum => {}

                    ObjectType::Max => unreachable!(),
                }
            }
        }
    }

    #[rustfmt::skip]
    fn visit_edges(&self, visitor: &impl Visitor) {
        match self.header.kind() {
            ObjectKind::Map => {
                // SAFETY: matched to this
                match unsafe { self.header.map_type().unwrap_unchecked() } {
                    MapType::Slot       => self.downcast_ref_match::<SlotMap>().visit_edges(visitor),
                    MapType::Max        => unreachable!(),
                }
            }
            ObjectKind::Object => {
                // SAFETY: matched to this
                match unsafe { self.header.object_type().unwrap_unchecked() } {
                    ObjectType::Slot        => self.downcast_ref_match::<SlotObject>().visit_edges(visitor),
                    ObjectType::Array       => self.downcast_ref_match::<Array>().visit_edges(visitor),
                    ObjectType::Activation  => self.downcast_ref_match::<ActivationObject>().visit_edges(visitor),
                    ObjectType::Quotation   => self.downcast_ref_match::<Quotation>().visit_edges(visitor),
                    ObjectType::Message     => self.downcast_ref_match::<Message>().visit_edges(visitor),
                    ObjectType::Thread      => self.downcast_ref_match::<ThreadObject>().visit_edges(visitor),
                    ObjectType::ByteArray | ObjectType::Float | ObjectType::BigNum => {}

                    ObjectType::Max => unreachable!(),
                }
            }
        }
    }
}

impl Object for Map {}
impl HeapObject for Map {
    const KIND: ObjectKind = ObjectKind::Map;
    const TYPE_BITS: u8 = MapType::Max as u8;

    #[rustfmt::skip]
    fn heap_size(&self) -> usize {
        // SAFETY: this is a map
        match unsafe { self.header.map_type().unwrap_unchecked() } {
            MapType::Slot       => self.downcast_ref_match::<SlotMap>().heap_size(),
            MapType::Max        => unreachable!()
        }
    }
}

// just like object, we dispatch here.
impl Visitable for Map {
    #[rustfmt::skip]
    fn visit_edges_mut(&mut self, visitor: &mut impl Visitor) {
        // SAFETY: this is a map
        match unsafe { self.header.map_type().unwrap_unchecked() } {
            MapType::Slot       => self.downcast_mut_match::<SlotMap>().visit_edges_mut(visitor),
            MapType::Max        => unreachable!()
        }
    }

    #[rustfmt::skip]
    fn visit_edges(&self, visitor: &impl Visitor) {
        // SAFETY: this is a map
        match unsafe { self.header.map_type().unwrap_unchecked() } {
            MapType::Slot       => self.downcast_ref_match::<SlotMap>().visit_edges(visitor),
            MapType::Max        => unreachable!()
        }
    }
}
