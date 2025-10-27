use crate::{
    Array, ArrayMap, Map, MapType, Object, ObjectKind, ObjectType, SlotMap, SlotObject, TaggedPtr,
    TaggedValue,
};

pub trait Visitable {
    fn visit_edges(&mut self, _visitor: &mut impl Visitor) {}
}

pub trait Visitor: Sized {
    fn visit(&mut self, value: TaggedValue) {
        let should_continue = self.visit_element(value);
        if !value.is_reference() || !should_continue {
            return;
        }
        let ptr = TaggedPtr::<Object>::from(value);
        let obj = unsafe { ptr.as_mut() };
        obj.visit_edges(self);
    }
    fn visit_element(&mut self, value: TaggedValue) -> bool;
}

pub struct MarkVisitor {}

impl Visitor for MarkVisitor {
    fn visit_element(&mut self, value: TaggedValue) -> bool {
        if value.is_small_int() {
            return false;
        }

        let reference = TaggedPtr::<Object>::from(value);
        let obj = unsafe { reference.as_mut() };

        if obj.header.is_marked() {
            return false;
        }

        obj.header.mark();
        true
    }
}

impl Visitable for Object {
    #[inline]
    fn visit_edges(&mut self, visitor: &mut impl Visitor) {
        match self.header.kind() {
            ObjectKind::Map => {
                let map = unsafe { std::mem::transmute::<_, &mut Map>(self) };
                map.visit_edges(visitor);
            }
            ObjectKind::Object => match self.header.object_type().unwrap() {
                ObjectType::Slot => {
                    let slot_object = unsafe { std::mem::transmute::<_, &mut SlotObject>(self) };
                    slot_object.visit_edges(visitor);
                }
                ObjectType::Array => {
                    let array_object = unsafe { std::mem::transmute::<_, &mut Array>(self) };
                    array_object.visit_edges(visitor);
                }
                ObjectType::ByteArray => (),
                _ => {
                    unimplemented!()
                }
            },
        }
    }
}

impl Visitable for Map {
    #[inline]
    fn visit_edges(&mut self, visitor: &mut impl Visitor) {
        match self.header.map_type() {
            Some(MapType::Slot) => unsafe {
                let sm: &mut SlotMap = &mut *(self as *mut Map as *mut SlotMap);
                sm.visit_edges(visitor);
            },
            Some(MapType::Array) => unsafe {
                let am: &mut ArrayMap = &mut *(self as *mut Map as *mut ArrayMap);
                am.visit_edges(visitor);
            },
            None => {
                panic!("visiting map type that doesnt exist")
            }
        }
    }
}

impl Visitable for SlotMap {
    #[inline]
    fn visit_edges(&mut self, visitor: &mut impl Visitor) {
        let _ = visitor;
    }
}

impl Visitable for ArrayMap {
    #[inline]
    fn visit_edges(&mut self, visitor: &mut impl Visitor) {
        let _ = visitor;
    }
}

impl Visitable for SlotObject {
    #[inline]
    fn visit_edges(&mut self, visitor: &mut impl Visitor) {
        self.slots().iter().for_each(|&slot| visitor.visit(slot));
    }
}

impl Visitable for Array {
    #[inline]
    fn visit_edges(&mut self, visitor: &mut impl Visitor) {
        self.fields().iter().for_each(|&v| visitor.visit(v));
    }
}

#[cfg(test)]
mod tests {
    use crate::{Header, HeaderFlags, MapType, TaggedI64, TaggedU64, TaggedUsize};

    use super::*;
    use std::alloc::{Layout, alloc_zeroed, dealloc};
    use std::mem::{align_of, size_of};
    use std::ptr::NonNull;

    fn layout_slot_object(slot_count: usize) -> Layout {
        let base = size_of::<SlotObject>();
        let elem = size_of::<TaggedValue>();
        let size = base + slot_count * elem;
        // SAFETY: SlotObject alignment is valid & non-zero.
        Layout::from_size_align(size, align_of::<SlotObject>()).unwrap()
    }

    fn layout_array(len: usize) -> Layout {
        let base = size_of::<Array>();
        let elem = size_of::<TaggedValue>();
        let size = base + len * elem;
        Layout::from_size_align(size, align_of::<Array>()).unwrap()
    }

    fn make_slot_map(assignable_slots: usize) -> Box<SlotMap> {
        let sm = SlotMap::new(TaggedU64::from(assignable_slots as u64));
        Box::new(sm)
    }

    fn make_array_map(len: usize) -> Box<ArrayMap> {
        let am = ArrayMap::new(TaggedUsize::from(len));
        Box::new(am)
    }

    unsafe fn write_trailing_values(base: *mut TaggedValue, values: &[TaggedValue]) {
        for (i, v) in values.iter().copied().enumerate() {
            unsafe { base.add(i).write(v) };
        }
    }

    fn alloc_slot_object(map: NonNull<SlotMap>, slots: &[TaggedValue]) -> NonNull<SlotObject> {
        let layout = layout_slot_object(slots.len());
        let raw = unsafe { alloc_zeroed(layout) as *mut SlotObject };
        let nn = NonNull::new(raw).expect("allocation failed");
        SlotObject::init(nn, map);
        unsafe {
            let slots_ptr = (*raw).slots.as_mut_ptr();
            write_trailing_values(slots_ptr, slots);
        }
        nn
    }

    fn alloc_array(map: NonNull<ArrayMap>, fields: &[TaggedValue]) -> NonNull<Array> {
        let layout = layout_array(fields.len());
        let raw = unsafe { alloc_zeroed(layout) as *mut Array };
        let nn = NonNull::new(raw).expect("allocation failed");
        Array::init(nn, map);
        unsafe {
            let fields_ptr = (*raw).fields.as_mut_ptr();
            write_trailing_values(fields_ptr, fields);
        }
        nn
    }

    unsafe fn dealloc_slot_object(ptr: NonNull<SlotObject>, slots: usize) {
        let layout = layout_slot_object(slots);
        unsafe { dealloc(ptr.as_ptr() as *mut u8, layout) };
    }

    unsafe fn dealloc_array(ptr: NonNull<Array>, len: usize) {
        let layout = layout_array(len);
        unsafe { dealloc(ptr.as_ptr() as *mut u8, layout) };
    }

    /// Helper to convert a NonNull<T> -> TaggedPtr<T> -> TaggedValue.
    fn tagged_value_from_ptr<T: Copy>(nn: NonNull<T>) -> TaggedValue
    where
        TaggedPtr<T>: Into<TaggedValue>,
    {
        let tp = TaggedPtr::<T>::from_nonnull(nn);
        tp.into()
    }

    // A minimal fake heap so we can construct MarkVisitor.
    struct DummyHeap;
    impl DummyHeap {
        fn new() -> Self {
            Self
        }
    }

    // ---------- tests ----------

    #[test]
    fn header_encode_decode_roundtrip_object_and_map() {
        let mut h = Header::encode_object(
            ObjectType::Array,
            3,
            HeaderFlags::PIN | HeaderFlags::LARGE,
            0xDEAD_BEEF,
        );
        assert_eq!(h.kind(), ObjectKind::Object);
        assert_eq!(h.object_type(), Some(ObjectType::Array));
        assert_eq!(h.age(), 3);
        assert!(h.flags().contains(HeaderFlags::PIN));
        assert!(h.flags().contains(HeaderFlags::LARGE));
        assert_eq!(h.data(), 0xDEAD_BEEF);

        h.set_map_type(MapType::Slot)
            .set_age(7)
            .set_flags(HeaderFlags::MARK | HeaderFlags::FORWARD)
            .set_data(123);
        assert_eq!(h.kind(), ObjectKind::Map);
        assert_eq!(h.map_type(), Some(MapType::Slot));
        assert_eq!(h.age(), 7);
        assert!(h.flags().contains(HeaderFlags::MARK));
        assert!(h.flags().contains(HeaderFlags::FORWARD));
        assert_eq!(h.data(), 123);
    }

    #[test]
    fn data_lo16_cache_helpers() {
        let mut h = Header::encode_object(ObjectType::Slot, 0, HeaderFlags::empty(), 0);
        assert_eq!(h.data_lo16(), 0);
        h.set_data_lo16(0xBEEF);
        assert_eq!(h.data_lo16(), 0xBEEF);
        // make sure upper bits preserved when we update lo16 only
        h.set_data(0xAAAA_0000);
        h.set_data_lo16(0x1234);
        assert_eq!(h.data(), 0xAAAA_1234);
    }

    #[test]
    fn slotobject_and_array_len_use_cached_u16() {
        // SlotObject cache
        let sm_small = make_slot_map(5);
        let so = {
            let so_ptr = alloc_slot_object(
                NonNull::from(sm_small.as_ref()),
                &[], // no actual slots written, just testing header cache
            );
            let so_ref = unsafe { so_ptr.as_ref() };
            assert_eq!(so_ref.assignable_slots(), 5);
            // now a big one that forces cache=0xFFFF and map fallback
            let sm_big = make_slot_map(u16::MAX as usize + 5);
            let so_ptr_big = alloc_slot_object(NonNull::from(sm_big.as_ref()), &[]);
            let so_big = unsafe { so_ptr_big.as_ref() };
            assert_eq!(so_big.assignable_slots(), u16::MAX as usize + 5);

            // clean up
            unsafe {
                dealloc_slot_object(so_ptr, 0);
                dealloc_slot_object(so_ptr_big, 0);
            }
        };

        // Array cache
        let am_small = make_array_map(7);
        let arr_ptr = alloc_array(
            NonNull::from(am_small.as_ref()),
            &vec![TaggedValue::from(TaggedI64::from(0)); 7],
        );
        let arr = unsafe { arr_ptr.as_ref() };
        assert_eq!(arr.len(), 7);

        let am_big = make_array_map(u16::MAX as usize + 1);
        let arr_ptr_big = alloc_array(
            NonNull::from(am_big.as_ref()),
            &vec![TaggedValue::from(TaggedI64::from(0)); u16::MAX as usize + 1],
        );
        let arr_big = unsafe { arr_ptr_big.as_ref() };
        assert_eq!(arr_big.len(), u16::MAX as usize + 1);

        unsafe {
            dealloc_array(arr_ptr, 7);
            dealloc_array(arr_ptr_big, u16::MAX as usize + 1);
        }
        let _ = so; // silence unused
    }

    #[test]
    fn visit_taggedvalue_ignores_small_int() {
        struct CountingVisitor(usize);
        impl Visitor for CountingVisitor {
            fn visit_element(&mut self, _v: TaggedValue) -> bool {
                self.0 += 1;
                true
            }
        }

        let v: TaggedValue = TaggedValue::from(TaggedI64::from(1234));
        let mut cv = CountingVisitor(0);
        cv.visit(v);
        assert_eq!(cv.0, 1);
    }

    #[test]
    fn slotobject_and_array_visit_their_edges() {
        // Build a tiny graph:
        //   root SlotObject( [ small-int, ptr->Array([small-int]) ] )
        // Each object also points to its Map via the .map field.
        let am = make_array_map(1);
        let arr_ptr = alloc_array(
            NonNull::from(am.as_ref()),
            &[TaggedValue::from(TaggedI64::from(7))],
        );

        let sm = make_slot_map(2);
        // Prepare slots: small int, then pointer to the Array as a TaggedValue
        let slots = [
            TaggedValue::from(TaggedI64::from(42)),
            tagged_value_from_ptr(arr_ptr),
        ];
        let so_ptr = alloc_slot_object(NonNull::from(sm.as_ref()), &slots);

        // Counting visitor that counts every value it *receives*
        struct CountingVisitor {
            pub count: usize,
        }
        impl Visitor for CountingVisitor {
            fn visit_element(&mut self, value: TaggedValue) -> bool {
                if value.is_small_int() {
                    return false;
                }
                self.count += 1;
                true
            }
        }
        let mut cv = CountingVisitor { count: 0 };

        cv.visit(TaggedPtr::from_nonnull(so_ptr).into());
        assert_eq!(cv.count, 2);

        unsafe {
            dealloc_array(arr_ptr, 1);
            dealloc_slot_object(so_ptr, 2);
        }
    }

    #[test]
    fn markvisitor_marks_reachable_objects_and_ignores_small_ints() {
        // Graph (roots = the TaggedValue pointing to root SlotObject):
        //   root SlotObject [ 42, ptr->Array([7]) ]
        // Reachables to mark: root SlotObject, its SlotMap, Array object, ArrayMap.
        // Unreachable: an isolated SlotObject (left unreferenced).
        let heap = DummyHeap::new();
        let mut marker = MarkVisitor {};

        // Allocate reachable array & maps
        let am = make_array_map(1);
        let arr_ptr = alloc_array(
            NonNull::from(am.as_ref()),
            &[TaggedValue::from(TaggedI64::from(7))],
        );
        let sm = make_slot_map(2);
        let slots = [
            TaggedValue::from(TaggedI64::from(42)),
            tagged_value_from_ptr(arr_ptr),
        ];
        let so_ptr = alloc_slot_object(NonNull::from(sm.as_ref()), &slots);

        // Allocate an unreachable object (and its map) to ensure it remains unmarked
        let sm_unreach = make_slot_map(1);
        let so_unreach_ptr = alloc_slot_object(
            NonNull::from(sm_unreach.as_ref()),
            &[TaggedValue::from(TaggedI64::from(0))],
        );

        // Sanity: all unmarked initially
        let root_obj = unsafe { &mut *(so_ptr.as_ptr() as *mut Object) };
        let arr_obj = unsafe { &mut *(arr_ptr.as_ptr() as *mut Object) };
        assert!(!root_obj.header.is_marked());
        assert!(!arr_obj.header.is_marked());
        assert!(!sm.as_ref().map.header.is_marked());
        assert!(!am.as_ref().map.header.is_marked());

        // Root as a TaggedValue
        let root_tv = tagged_value_from_ptr(so_ptr);

        // Run mark from the root value
        marker.visit(root_tv);
        marker.visit(TaggedPtr::from_nonnull(NonNull::from(sm.as_ref())).into());
        marker.visit(TaggedPtr::from_nonnull(NonNull::from(am.as_ref())).into());

        // Now all reachable ones must be marked
        assert!(
            root_obj.header.is_marked(),
            "root SlotObject should be marked"
        );
        assert!(
            sm.as_ref().map.header.is_marked(),
            "SlotMap should be marked"
        );
        assert!(arr_obj.header.is_marked(), "Array object should be marked");
        assert!(
            am.as_ref().map.header.is_marked(),
            "ArrayMap should be marked"
        );

        // Unreachable remains unmarked
        let unreach_obj = unsafe { &mut *(so_unreach_ptr.as_ptr() as *mut Object) };
        assert!(
            !unreach_obj.header.is_marked(),
            "unreachable object must stay unmarked"
        );

        unsafe {
            dealloc_array(arr_ptr, 1);
            dealloc_slot_object(so_ptr, 2);
            dealloc_slot_object(so_unreach_ptr, 1);
        }
    }
}
