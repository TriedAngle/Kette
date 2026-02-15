mod value;
mod handle;
mod header;
mod slot;
mod map;
mod objects;
mod special;

pub use value::Value;
pub use handle::Tagged;
pub use header::{Header, HeaderFlags, ObjectType};
pub use slot::{Slot, SlotFlags};
pub use map::{Map, init_map, map_allocation_size};
pub use objects::{
    SlotObject, slot_object_allocation_size,
    Array, ByteArray,
    Code, Block,
    BigNum, Alien, Str, Ratio,
};
pub use special::SpecialObjects;

#[cfg(test)]
mod tests {
    use super::*;

    // ── Value tagging ──────────────────────────────────────────────

    #[test]
    fn fixnum_round_trip() {
        for &n in &[0i64, 1, -1, 42, -42, i64::MAX >> 1, i64::MIN >> 1] {
            let v = Value::from_i64(n);
            assert!(v.is_fixnum());
            assert!(!v.is_ref());
            assert!(!v.is_header());
            assert_eq!(unsafe { v.to_i64() }, n);
        }
    }

    #[test]
    fn fixnum_zero_is_zero_bits() {
        let v = Value::from_i64(0);
        assert_eq!(v.raw(), 0);
    }

    #[test]
    fn ref_tagging() {
        // Simulate an 8-byte aligned pointer.
        let dummy: u64 = 0;
        let ptr = &dummy as *const u64;
        let v = Value::from_ptr(ptr);
        assert!(v.is_ref());
        assert!(!v.is_fixnum());
        assert!(!v.is_header());
        assert_eq!(v.ref_bits(), ptr as u64);
    }

    #[test]
    fn header_tag_detected() {
        let hdr = Header::new(ObjectType::Slots);
        // Read the 8-byte header as a Value.
        let raw = unsafe { *((&hdr) as *const Header as *const u64) };
        let v = Value::from_raw(raw);
        assert!(v.is_header());
        assert!(!v.is_fixnum());
        assert!(!v.is_ref());
    }

    // ── Tagged ───────────────────────────────────────────────

    #[test]
    fn handle_fixnum_helpers() {
        let h = Tagged::<()>::from_value(Value::from_i64(42));
        assert!(h.is_fixnum());
        unsafe {
            assert_eq!(h.as_i64(), 42);
            assert_eq!(h.as_u64(), 42);
            assert_eq!(h.as_usize(), 42);
        }
    }

    #[test]
    fn handle_ref_round_trip() {
        let data: u64 = 0xCAFE;
        let h = Tagged::<u64>::from_value(Value::from_ptr(&data));
        assert!(h.is_ref());
        unsafe {
            assert_eq!(*h.as_ref(), 0xCAFE);
        }
    }

    // ── Header ─────────────────────────────────────────────────────

    #[test]
    fn header_object_type() {
        for (i, &ty) in [
            ObjectType::Slots,
            ObjectType::Map,
            ObjectType::Array,
            ObjectType::ByteArray,
            ObjectType::Code,
            ObjectType::Block,
            ObjectType::BigNum,
            ObjectType::Alien,
            ObjectType::Str,
            ObjectType::Ratio,
        ]
        .iter()
        .enumerate()
        {
            let h = Header::new(ty);
            assert_eq!(h.object_type(), ty, "type mismatch at index {i}");
        }
    }

    #[test]
    fn header_flags() {
        let h = Header::new(ObjectType::Slots);
        assert!(!h.has_flag(HeaderFlags::PINNED));

        h.add_flag(HeaderFlags::PINNED);
        assert!(h.has_flag(HeaderFlags::PINNED));

        h.add_flag(HeaderFlags::REMEMBERED);
        assert!(h.has_flag(HeaderFlags::PINNED));
        assert!(h.has_flag(HeaderFlags::REMEMBERED));

        h.remove_flag(HeaderFlags::PINNED);
        assert!(!h.has_flag(HeaderFlags::PINNED));
        assert!(h.has_flag(HeaderFlags::REMEMBERED));
    }

    #[test]
    fn header_age() {
        let h = Header::new(ObjectType::Map);
        assert_eq!(h.age(), 0);
        h.set_age(5);
        assert_eq!(h.age(), 5);
        let prev = h.increment_age();
        assert_eq!(prev, 5);
        assert_eq!(h.age(), 6);
    }

    // ── Slots ──────────────────────────────────────────────────────

    #[test]
    fn slot_flags_round_trip() {
        let flags = SlotFlags::ASSIGNABLE.with(SlotFlags::ENUMERABLE);
        let s = Slot::new(flags, Value::from_i64(0), Value::from_i64(16));
        assert!(s.is_assignable());
        assert!(!s.is_assignment());
        assert!(!s.is_constant());
        assert!(!s.is_parent());
        assert!(s.flags().contains(SlotFlags::ENUMERABLE));
    }

    #[test]
    fn slot_assignment_flag() {
        let flags = SlotFlags::ASSIGNMENT.with(SlotFlags::ENUMERABLE);
        let s = Slot::new(flags, Value::from_i64(0), Value::from_i64(16));
        assert!(s.is_assignment());
        assert!(!s.is_assignable());
    }

    // ── Map layout ─────────────────────────────────────────────────

    #[test]
    fn map_allocation_sizes() {
        assert_eq!(map_allocation_size(0), 32);
        assert_eq!(map_allocation_size(1), 32 + 24);
        assert_eq!(map_allocation_size(3), 32 + 3 * 24);
    }

    // ── SlotObject layout ──────────────────────────────────────────

    #[test]
    fn slot_object_values_offset() {
        assert_eq!(SlotObject::VALUES_OFFSET, 16);
    }

    #[test]
    fn slot_object_allocation_sizes() {
        assert_eq!(slot_object_allocation_size(0), 16);
        assert_eq!(slot_object_allocation_size(3), 16 + 3 * 8);
    }
}
