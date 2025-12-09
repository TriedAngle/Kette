use std::mem;

pub mod activation;
pub mod arrays;
pub mod bytearrays;
pub mod executable;
pub mod message;
pub mod parser;
pub mod quotations;
pub mod slots;
pub mod threads;

use crate::{
    ActivationObject, Array, ByteArray, LookupResult, Message, Method,
    MethodMap, Quotation, QuotationMap, Selector, SlotMap, SlotObject, Value,
    ValueTag, Visitable, VisitedLink, Visitor,
};

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
    Activation = 0b00100,
    Method = 0b00101,
    Quotation = 0b00111,
    Message = 0b01000,
    Max = 0b11111,
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

// TODO: in our current garbage collector iteration objects do not move, thus pin does nothing.
// in future iterations of the garbage collector, we will move objects to defragment.
// if objects are currently in a FFI context, we will pin them so they don't move.
bitflags::bitflags! {
    pub struct HeaderFlags: u8 {
        const MARK    = 1 << 0;
        const PIN     = 1 << 1;
        const LARGE   = 1 << 2;
    }
}

// ValueTag::Header + ObjectKind::Object + ObjectType::Max
pub const HEADER_FREE: u8 = 0b11111011;

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
#[derive(Debug, Copy, Clone, Hash)]
pub struct Header(u64);

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

    const DATA_LO16_MASK: u32 = 0xFFFF; // cached size/slots

    #[inline]
    pub const fn zeroed() -> Self {
        Self(0)
    }

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
            | ((((type_bits as u64) & 0x1F) << Self::TYPE_SHIFT)
                & Self::TYPE_MASK)
            | (((age as u64) & 0xF) << Self::AGE_SHIFT)
            | (((flags.bits() as u64) & 0xF) << Self::FLAGS_SHIFT)
            | ((data as u64) << Self::DATA_SHIFT);
        Header(inner)
    }

    /// Encode an Object header.
    #[inline]
    pub fn encode_object(
        ty: ObjectType,
        age: u8,
        flags: HeaderFlags,
        data: u32,
    ) -> Header {
        Self::encode_raw(ObjectKind::Object, ty as u8, age, flags, data)
    }

    /// Encode a Map header.
    #[inline]
    pub fn encode_map(
        ty: MapType,
        age: u8,
        flags: HeaderFlags,
        data: u32,
    ) -> Header {
        Self::encode_raw(ObjectKind::Map, ty as u8, age, flags, data)
    }

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
            0b00100 => ObjectType::Activation,
            0b00101 => ObjectType::Method,
            0b00111 => ObjectType::Quotation,
            0b01000 => ObjectType::Message,
            0b11111 => ObjectType::Max,
            _ => unreachable!("object type doesn't exist"),
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
            // 1 => MapType::Array,
            _ => return None,
        })
    }

    #[inline]
    pub fn is_free(&self) -> bool {
        (self.0 as u8) == HEADER_FREE
    }

    #[inline]
    pub fn new_free(size: u64) -> Self {
        debug_assert!(
            size <= 0x00FF_FFFF_FFFF_FFFF,
            "Size must fit in 56 bits"
        );

        let mut bits = HEADER_FREE as u64;
        bits |= size << 8;
        Header(bits)
    }

    #[inline]
    pub fn age(self) -> u8 {
        ((self.0 & Self::AGE_MASK) >> Self::AGE_SHIFT) as u8
    }

    #[inline]
    pub fn flags(self) -> HeaderFlags {
        HeaderFlags::from_bits_truncate(
            ((self.0 & Self::FLAGS_MASK) >> Self::FLAGS_SHIFT) as u8,
        )
    }

    #[inline]
    pub fn data(self) -> u32 {
        ((self.0 & Self::DATA_MASK) >> Self::DATA_SHIFT) as u32
    }

    #[inline]
    pub fn set_kind(&mut self, kind: ObjectKind) -> &mut Self {
        self.0 = (self.0 & !Self::KIND_MASK)
            | (((kind as u64) & 0x1) << Self::KIND_SHIFT);
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
        self.0 = (self.0 & !Self::AGE_MASK)
            | (((age as u64) & 0xF) << Self::AGE_SHIFT);
        self
    }

    #[inline]
    pub fn set_flags(&mut self, flags: HeaderFlags) -> &mut Self {
        self.0 = (self.0 & !Self::FLAGS_MASK)
            | (((flags.bits() as u64) & 0xF) << Self::FLAGS_SHIFT);
        self
    }

    #[inline]
    pub fn set_data(&mut self, data: u32) -> &mut Self {
        self.0 =
            (self.0 & !Self::DATA_MASK) | ((data as u64) << Self::DATA_SHIFT);
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
    /// # Safety
    /// internal api
    #[inline]
    pub unsafe fn init(&mut self, ty: MapType) {
        self.header = Header::encode_map(ty, 0, HeaderFlags::empty(), 0);
    }

    #[inline]
    pub fn map_type(&self) -> Option<MapType> {
        self.header.map_type()
    }
}
// TODO: use this (maybe?) and maybe move this into heap
// #[repr(C)]
// #[derive(Debug, Copy, Clone)]
// pub struct FreeLocation {
//     pub header: Header,
//     pub next: Option<*mut FreeLocation>,
// }
// impl FreeLocation {
//     #[inline]
//     pub fn new(size: u64, next: Option<*mut FreeLocation>) -> Self {
//         Self {
//             header: Header::new_free(size),
//             next,
//         }
//     }

//     /// Set the next free location pointer
//     #[inline]
//     pub fn set_next(&mut self, next: Option<*mut FreeLocation>) {
//         self.next = next;
//     }

//     /// Get the next free location pointer
//     #[inline]
//     pub fn get_next(&self) -> Option<*mut FreeLocation> {
//         self.next
//     }

//     /// Get the size of this free memory block
//     #[inline]
//     pub fn size(&self) -> u64 {
//         debug_assert!(self.header.is_free(), "Header must be a free object");
//         self.header.0 >> 8
//     }

//     /// Update the size of this free memory block
//     #[inline]
//     pub fn set_size(&mut self, size: u64) {
//         self.header = Header::new_free(size);
//     }
// }

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
            ObjectType::Activation => {
                // SAFETY: checked
                let activation = unsafe {
                    mem::transmute::<&HeapValue, &ActivationObject>(self)
                };
                activation.lookup(selector, link)
            }
            _ => unimplemented!("object type not implemented"),
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
            ObjectType::Message => {
                // SAFETY: checked
                let message = unsafe {
                    std::mem::transmute::<&mut HeapValue, &mut Message>(self)
                };
                message.visit_edges_mut(visitor);
            }
            ObjectType::ByteArray => (),
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
            ObjectType::Message => {
                // SAFETY: checked
                let message = unsafe {
                    std::mem::transmute::<&HeapValue, &Message>(self)
                };
                message.visit_edges(visitor);
            }
            ObjectType::ByteArray => (),
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
