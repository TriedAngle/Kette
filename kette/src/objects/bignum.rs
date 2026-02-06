use std::{alloc::Layout, mem};

use crate::{
    Header, HeapObject, LookupResult, Object, ObjectKind, ObjectType, Selector,
    Tagged, Visitable, VisitedLink,
};

#[repr(C)]
#[derive(Debug)]
pub struct BigNum {
    pub header: Header,
    pub sign: i8,
    pub len: Tagged<usize>,
    pub data: [u64; 0],
}

impl BigNum {
    const FIXNUM_MAX: i64 = (1_i64 << 62) - 1;

    pub fn init(&mut self, sign: i8, limbs: &[u64]) {
        self.header = Header::new_object(ObjectType::BigNum);
        let len = limbs.len();
        if len == 0 {
            self.sign = 0;
            self.len = 0usize.into();
            return;
        }

        self.sign = sign;
        self.len = len.into();
        let dest = self.data.as_mut_ptr();
        // SAFETY: allocation accounts for limbs length
        unsafe { std::ptr::copy_nonoverlapping(limbs.as_ptr(), dest, len) };
    }

    pub fn init_zeroed(&mut self, sign: i8, len: usize) {
        self.header = Header::new_object(ObjectType::BigNum);
        if len == 0 {
            self.sign = 0;
            self.len = 0usize.into();
            return;
        }
        self.sign = sign;
        self.len = len.into();
        let dest = self.data.as_mut_ptr();
        // SAFETY: allocation accounts for limbs length
        unsafe { std::ptr::write_bytes(dest, 0, len) };
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.len.into()
    }

    #[inline]
    pub fn limbs(&self) -> &[u64] {
        let len = self.len();
        // SAFETY: bignum must be correctly sized
        unsafe { std::slice::from_raw_parts(self.data.as_ptr(), len) }
    }

    #[inline]
    pub fn limbs_mut(&mut self) -> &mut [u64] {
        let len = self.len();
        // SAFETY: bignum must be correctly sized
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

    #[must_use]
    pub fn required_layout(len: usize) -> Layout {
        let base = Layout::new::<Self>();
        let limbs = Layout::array::<u64>(len).expect("create layout");
        let (layout, _) = base.extend(limbs).expect("extend layout");
        layout
    }
}

impl Object for BigNum {
    fn lookup(
        &self,
        selector: Selector,
        link: Option<&VisitedLink>,
    ) -> LookupResult {
        let traits = selector.vm.specials.bignum_traits;
        traits.lookup(selector, link)
    }
}

impl HeapObject for BigNum {
    const KIND: ObjectKind = ObjectKind::Object;
    const TYPE_BITS: u8 = ObjectType::BigNum as u8;

    fn heap_size(&self) -> usize {
        mem::size_of::<Self>() + self.len() * mem::size_of::<u64>()
    }
}

impl Visitable for BigNum {
    #[inline]
    fn visit_edges_mut(&mut self, _visitor: &mut impl crate::Visitor) {}

    #[inline]
    fn visit_edges(&self, _visitor: &impl crate::Visitor) {}
}

#[cfg(test)]
mod tests {
    use crate::{Allocator, Heap, HeapSettings};

    #[test]
    fn bignum_alloc_from_u64_sets_sign_and_limb() {
        let heap = Heap::new(HeapSettings::default());
        let mut heap = heap.proxy();

        let bn = heap.allocate_bignum_from_u64(42);
        assert_eq!(bn.sign, 1);
        assert_eq!(bn.len(), 1);
        assert_eq!(bn.limbs()[0], 42);
    }

    #[test]
    fn bignum_alloc_from_i64_sets_sign_and_limb() {
        let heap = Heap::new(HeapSettings::default());
        let mut heap = heap.proxy();

        let bn = heap.allocate_bignum_from_i64(-17);
        assert_eq!(bn.sign, -1);
        assert_eq!(bn.len(), 1);
        assert_eq!(bn.limbs()[0], 17);
    }

    #[test]
    fn bignum_alloc_from_i128_spans_two_limbs() {
        let heap = Heap::new(HeapSettings::default());
        let mut heap = heap.proxy();

        let value = (1_i128 << 70) + 3;
        let bn = heap.allocate_bignum_from_i128(value);
        assert_eq!(bn.sign, 1);
        assert_eq!(bn.len(), 2);
        assert_eq!(bn.limbs()[0], 3);
        assert_eq!(bn.limbs()[1], 1_u64 << 6);
    }

    #[test]
    fn bignum_to_fixnum_checked_bounds() {
        let heap = Heap::new(HeapSettings::default());
        let mut heap = heap.proxy();

        let ok = heap.allocate_bignum_from_i64((1_i64 << 62) - 1);
        assert_eq!(ok.to_fixnum_checked(), Some((1_i64 << 62) - 1));

        let neg = heap.allocate_bignum_from_i64(-(1_i64 << 62));
        assert_eq!(neg.to_fixnum_checked(), Some(-(1_i64 << 62)));

        let too_big = heap.allocate_bignum_from_u64(1_u64 << 62);
        assert_eq!(too_big.to_fixnum_checked(), None);
    }
}
