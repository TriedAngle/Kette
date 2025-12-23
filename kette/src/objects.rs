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
    ActivationObject, Array, ByteArray, Float, LookupResult, Message, Method,
    MethodMap, Quotation, QuotationMap, Selector, SlotMap, SlotObject,
    StackEffect, Value, ValueTag, Visitable, VisitedLink, Visitor,
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
    Method      = 0b00101,
    Effect      = 0b00110,
    Quotation   = 0b00111,
    Message     = 0b01000,
    Float       = 0b01001,
    BigNum      = 0b01010,
    Max         = 0b11111,
}

/// What kind of map this is. Lives in the unified 5-bit TYPE field
/// when `kind == Kind::Map`.
#[repr(u8)]
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum MapType {
    Slot = 0b000,
    // Array = 0b001,
    Method = 0b100,
    Quotation = 0b101,
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
    fn header(&self) -> &Header {
        // SAFETY: every heap object has header
        unsafe { std::mem::transmute::<&Self, &Header>(self) }
    }
    fn header_mut(&mut self) -> &mut Header {
        // SAFETY: every heap object has header
        unsafe { std::mem::transmute::<&mut Self, &mut Header>(self) }
    }

    fn heap_size(&self) -> usize {
        mem::size_of::<Self>()
    }
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
    pub fn new_object(ty: ObjectType) -> Self {
        Self::new_raw(ObjectKind::Object, ty as u8, HeaderFlags::empty(), 0)
    }

    #[inline]
    pub fn new_map(ty: MapType) -> Self {
        Self::new_raw(ObjectKind::Map, ty as u8, HeaderFlags::empty(), 0)
    }

    #[inline]
    pub fn new_object2(ty: ObjectType, flags: HeaderFlags, data: u32) -> Self {
        Self::new_raw(ObjectKind::Object, ty as u8, flags, data)
    }

    #[inline]
    pub fn new_map2(ty: MapType, flags: HeaderFlags, data: u32) -> Self {
        Self::new_raw(ObjectKind::Map, ty as u8, flags, data)
    }

    #[inline]
    fn new_raw(
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
            0b00101 => ObjectType::Method,
            0b00110 => ObjectType::Effect,
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
            0b100 => MapType::Method,
            0b101 => MapType::Quotation,
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
}

impl Object for HeapValue {
    fn lookup(
        &self,
        selector: Selector,
        link: Option<&VisitedLink>,
    ) -> LookupResult {
        match self
            .header
            .object_type()
            .expect("maps do not implement lookup, must be object")
        {
            ObjectType::Slot => {
                // SAFETY: checked
                let slot_object = unsafe {
                    std::mem::transmute::<&HeapValue, &SlotObject>(self)
                };
                slot_object.lookup(selector, link)
            }
            ObjectType::Array => {
                // SAFETY: checked
                let array =
                    unsafe { std::mem::transmute::<&HeapValue, &Array>(self) };
                array.lookup(selector, link)
            }
            ObjectType::ByteArray => {
                // SAFETY: checked
                let byte_array = unsafe {
                    std::mem::transmute::<&HeapValue, &ByteArray>(self)
                };
                byte_array.lookup(selector, link)
            }
            ObjectType::Method => {
                // SAFETY: checked
                let slot_object =
                    unsafe { std::mem::transmute::<&HeapValue, &Method>(self) };
                slot_object.lookup(selector, link)
            }
            ObjectType::Effect => {
                // SAFETY: checked
                let slot_object = unsafe {
                    std::mem::transmute::<&HeapValue, &StackEffect>(self)
                };
                slot_object.lookup(selector, link)
            }
            ObjectType::Activation => {
                // SAFETY: checked
                let activation = unsafe {
                    mem::transmute::<&HeapValue, &ActivationObject>(self)
                };
                activation.lookup(selector, link)
            }
            ObjectType::Quotation => {
                // SAFETY: checked
                let quotation = unsafe {
                    std::mem::transmute::<&HeapValue, &Quotation>(self)
                };
                quotation.lookup(selector, link)
            }
            ObjectType::Float => {
                // SAFETY: checked
                let float =
                    unsafe { std::mem::transmute::<&HeapValue, &Float>(self) };
                float.lookup(selector, link)
            }
            ObjectType::BigNum => {
                // SAFETY: checked
                unimplemented!()
            }
            ObjectType::Message | ObjectType::Max => {
                unreachable!("illegal object type for lookup")
            }
        }
    }
}
impl HeapObject for HeapValue {
    fn heap_size(&self) -> usize {
        let obj = match self.header.kind() {
            ObjectKind::Map => {
                // SAFETY: checked
                let map =
                    unsafe { std::mem::transmute::<&HeapValue, &Map>(self) };
                return map.heap_size();
            }
            ObjectKind::Object => self,
        };

        // SAFETY: checked
        match unsafe { obj.header.object_type().unwrap_unchecked() } {
            ObjectType::Slot => {
                // SAFETY: checked
                let slot_object = unsafe {
                    std::mem::transmute::<&HeapValue, &SlotObject>(self)
                };
                slot_object.heap_size()
            }
            ObjectType::Array => {
                // SAFETY: checked
                let array_object =
                    unsafe { std::mem::transmute::<&HeapValue, &Array>(self) };
                array_object.heap_size()
            }
            ObjectType::Activation => {
                // SAFETY: checked
                let activation = unsafe {
                    std::mem::transmute::<&HeapValue, &ActivationObject>(self)
                };
                activation.heap_size()
            }
            ObjectType::Quotation => {
                // SAFETY: checked
                let quotation = unsafe {
                    std::mem::transmute::<&HeapValue, &Quotation>(self)
                };
                quotation.heap_size()
            }
            ObjectType::Method => {
                // SAFETY: checked
                let method =
                    unsafe { std::mem::transmute::<&HeapValue, &Method>(self) };
                method.heap_size()
            }
            ObjectType::Effect => {
                // SAFETY: checked
                let effect = unsafe {
                    std::mem::transmute::<&HeapValue, &StackEffect>(self)
                };
                effect.heap_size()
            }
            ObjectType::Message => {
                // SAFETY: checked
                let message = unsafe {
                    std::mem::transmute::<&HeapValue, &Message>(self)
                };
                message.heap_size()
            }
            ObjectType::ByteArray => {
                // SAFETY: checked
                let message = unsafe {
                    std::mem::transmute::<&HeapValue, &ByteArray>(self)
                };
                message.heap_size()
            }
            ObjectType::Float => {
                // SAFETY: checked
                let message =
                    unsafe { std::mem::transmute::<&HeapValue, &Float>(self) };
                message.heap_size()
            }
            ObjectType::BigNum => {
                unimplemented!()
            }
            ObjectType::Max => unreachable!(),
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
    #[inline]
    fn visit_edges_mut(&mut self, visitor: &mut impl Visitor) {
        match self.header.kind() {
            ObjectKind::Map => {
                // SAFETY: checked
                let map = unsafe {
                    std::mem::transmute::<&mut HeapValue, &mut Map>(self)
                };
                map.visit_edges_mut(visitor);
                return;
            }
            ObjectKind::Object => (),
        };

        // SAFETY: checked
        match unsafe { self.header.object_type().unwrap_unchecked() } {
            ObjectType::Slot => {
                // SAFETY: checked
                let slot_object = unsafe {
                    std::mem::transmute::<&mut HeapValue, &mut SlotObject>(self)
                };
                slot_object.visit_edges_mut(visitor);
            }
            ObjectType::Array => {
                // SAFETY: checked
                let array_object = unsafe {
                    std::mem::transmute::<&mut HeapValue, &mut Array>(self)
                };
                array_object.visit_edges_mut(visitor);
            }
            ObjectType::Activation => {
                // SAFETY: checked
                let activation = unsafe {
                    std::mem::transmute::<&mut HeapValue, &mut ActivationObject>(
                        self,
                    )
                };
                activation.visit_edges_mut(visitor);
            }
            ObjectType::Quotation => {
                // SAFETY: checked
                let quotation = unsafe {
                    std::mem::transmute::<&mut HeapValue, &mut Quotation>(self)
                };
                quotation.visit_edges_mut(visitor);
            }
            ObjectType::Method => {
                // SAFETY: checked
                let method = unsafe {
                    std::mem::transmute::<&mut HeapValue, &mut Method>(self)
                };
                method.visit_edges_mut(visitor);
            }
            ObjectType::Effect => {
                // SAFETY: checked
                let effect = unsafe {
                    std::mem::transmute::<&mut HeapValue, &mut StackEffect>(
                        self,
                    )
                };
                effect.visit_edges_mut(visitor)
            }
            ObjectType::Message => {
                // SAFETY: checked
                let message = unsafe {
                    std::mem::transmute::<&mut HeapValue, &mut Message>(self)
                };
                message.visit_edges_mut(visitor);
            }
            ObjectType::ByteArray | ObjectType::Float | ObjectType::BigNum => {}
            ObjectType::Max => unreachable!(),
        };
    }

    #[inline]
    fn visit_edges(&self, visitor: &impl Visitor) {
        let obj = match self.header.kind() {
            ObjectKind::Map => {
                // SAFETY: checked
                let map =
                    unsafe { std::mem::transmute::<&HeapValue, &Map>(self) };
                map.visit_edges(visitor);
                return;
            }
            ObjectKind::Object => self,
        };

        // SAFETY: checked
        match unsafe { obj.header.object_type().unwrap_unchecked() } {
            ObjectType::Slot => {
                // SAFETY: checked
                let slot_object = unsafe {
                    std::mem::transmute::<&HeapValue, &SlotObject>(self)
                };
                slot_object.visit_edges(visitor);
            }
            ObjectType::Array => {
                // SAFETY: checked
                let array_object =
                    unsafe { std::mem::transmute::<&HeapValue, &Array>(self) };
                array_object.visit_edges(visitor);
            }
            ObjectType::Activation => {
                // SAFETY: checked
                let activation = unsafe {
                    std::mem::transmute::<&HeapValue, &ActivationObject>(self)
                };
                activation.visit_edges(visitor);
            }
            ObjectType::Quotation => {
                // SAFETY: checked
                let quotation = unsafe {
                    std::mem::transmute::<&HeapValue, &Quotation>(self)
                };
                quotation.visit_edges(visitor);
            }
            ObjectType::Method => {
                // SAFETY: checked
                let method =
                    unsafe { std::mem::transmute::<&HeapValue, &Method>(self) };
                method.visit_edges(visitor);
            }
            ObjectType::Effect => {
                // SAFETY: checked
                let effect = unsafe {
                    std::mem::transmute::<&HeapValue, &StackEffect>(self)
                };
                effect.visit_edges(visitor)
            }
            ObjectType::Message => {
                // SAFETY: checked
                let message = unsafe {
                    std::mem::transmute::<&HeapValue, &Message>(self)
                };
                message.visit_edges(visitor);
            }
            ObjectType::ByteArray | ObjectType::Float | ObjectType::BigNum => {}
            ObjectType::Max => unreachable!(),
        };
    }
}

impl Object for Map {}
impl HeapObject for Map {
    fn heap_size(&self) -> usize {
        // SAFETY: this is a map
        match unsafe { self.header.map_type().unwrap_unchecked() } {
            MapType::Slot => {
                // SAFETY: checked
                let map =
                    unsafe { std::mem::transmute::<&Map, &SlotMap>(self) };
                map.heap_size()
            }
            MapType::Method => {
                // SAFETY: checked
                let map =
                    unsafe { std::mem::transmute::<&Map, &MethodMap>(self) };
                map.heap_size()
            }
            MapType::Quotation => {
                // SAFETY: checked
                let map =
                    unsafe { std::mem::transmute::<&Map, &QuotationMap>(self) };
                map.heap_size()
            }
        }
    }
}

// just like object, we dispatch here.
impl Visitable for Map {
    #[inline]
    fn visit_edges_mut(&mut self, visitor: &mut impl Visitor) {
        match self.header.map_type() {
            // SAFETY: checked
            Some(MapType::Slot) => unsafe {
                let sm: &mut SlotMap = &mut *(self as *mut Map as *mut _);
                sm.visit_edges_mut(visitor);
            },
            // SAFETY: checked
            Some(MapType::Method) => unsafe {
                let sm: &mut MethodMap = &mut *(self as *mut Map as *mut _);
                sm.visit_edges_mut(visitor);
            },
            // SAFETY: checked
            Some(MapType::Quotation) => unsafe {
                let sm: &mut QuotationMap = &mut *(self as *mut Map as *mut _);
                sm.visit_edges_mut(visitor);
            },
            None => {
                panic!("visiting map type that doesnt exist")
            }
        }
    }

    #[inline]
    fn visit_edges(&self, visitor: &impl Visitor) {
        match self.header.map_type() {
            // SAFETY: checked
            Some(MapType::Slot) => unsafe {
                let sm: &SlotMap = &*(self as *const Map as *const _);
                sm.visit_edges(visitor);
            },
            // SAFETY: checked
            Some(MapType::Method) => unsafe {
                let sm: &MethodMap = &*(self as *const Map as *const _);
                sm.visit_edges(visitor);
            },
            // SAFETY: checked
            Some(MapType::Quotation) => unsafe {
                let sm: &QuotationMap = &*(self as *const Map as *const _);
                sm.visit_edges(visitor);
            },
            None => {
                panic!("visiting map type that doesnt exist")
            }
        }
    }
}
