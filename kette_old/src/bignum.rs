use std::mem;

use crate::gc::GarbageCollector;
use crate::object::{ObjectHeader, ObjectRef};

#[repr(C)]
pub struct BigNum {
    pub header: ObjectHeader,
    pub meta: ObjectRef,
}

#[allow(unused)]
impl BigNum {
    pub fn required_size(size: usize) -> usize {
        size + mem::size_of::<Self>()
    }
    pub fn encode_meta(size: u64, negative: bool) -> ObjectRef {
        debug_assert!(size < (1 << 62), "size too large for BigNum");
        let mut bits = size;
        if negative {
            bits |= 1 << 62;
        }
        unsafe { ObjectRef::from_int(bits as i64) }
    }

    pub fn decode_meta(&self) -> (u64, bool) {
        let bits = unsafe { self.meta.as_int_unchecked() as u64 };
        let size = bits & ((1 << 62) - 1);
        let negative = (bits & (1 << 62)) != 0;
        (size, negative)
    }

    pub fn size(&self) -> u64 {
        self.decode_meta().0
    }

    pub fn is_negative(&self) -> bool {
        self.decode_meta().1
    }

    pub fn set_size(&mut self, size: u64) {
        debug_assert!(size < (1 << 62), "size too large for BigNum");
        let negative = self.is_negative();
        self.meta = Self::encode_meta(size, negative);
    }

    pub fn set_negative(&mut self, negative: bool) {
        let size = self.size();
        self.meta = Self::encode_meta(size, negative);
    }

    unsafe fn order_by_abs(
        lhs: *mut BigNum,
        rhs: *mut BigNum,
    ) -> (*mut BigNum, *mut BigNum, bool) {
        let (lhs_size, _) = (*lhs).decode_meta();
        let (rhs_size, _) = (*rhs).decode_meta();

        if lhs_size >= rhs_size {
            (lhs, rhs, false)
        } else {
            (rhs, lhs, true)
        }
    }

    pub unsafe fn digits(&self) -> *mut u8 {
        (self as *const BigNum as *mut u8).add(std::mem::size_of::<BigNum>())
    }
    unsafe fn get_digit(&self, idx: usize) -> u8 {
        if idx < self.size() as usize {
            *self.digits().add(idx)
        } else {
            0
        }
    }

    unsafe fn set_digit(&mut self, idx: usize, val: u8) {
        assert!(idx < self.size() as usize);
        *self.digits().add(idx) = val;
    }

    pub unsafe fn copy_digits(src: *const u8, dest: *mut u8, count: usize) {
        std::ptr::copy_nonoverlapping(src, dest, count);
    }

    pub unsafe fn zero_digits(dest: *mut u8, count: usize) {
        std::ptr::write_bytes(dest, 0, count);
    }

    pub unsafe fn from_bytes(
        gc: &mut GarbageCollector,
        bytes: &[u8],
        negative: bool,
    ) -> *mut BigNum {
        let num = gc.allocate_bignum(bytes.len() as u64, negative);
        Self::copy_digits(bytes.as_ptr(), (*num).digits(), bytes.len());
        num
    }

    pub unsafe fn add(
        lhs: *mut BigNum,
        rhs: *mut BigNum,
        gc: &mut GarbageCollector,
    ) -> *mut BigNum {
        let (lhs_size, lhs_neg) = (*lhs).decode_meta();
        let (rhs_size, rhs_neg) = (*rhs).decode_meta();

        if lhs_neg != rhs_neg {
            if lhs_neg {
                return Self::sub(rhs, lhs, gc);
            } else {
                return Self::sub(lhs, rhs, gc);
            }
        }

        let (bigger, smaller, _) = Self::order_by_abs(lhs, rhs);
        let max_size = (*bigger).size() as usize;
        let min_size = (*smaller).size() as usize;

        let result = gc.allocate_bignum(max_size as u64 + 1, lhs_neg);

        let mut carry = 0u8;
        for i in 0..max_size {
            let sum = (*bigger).get_digit(i) as u16
                + (*smaller).get_digit(i) as u16
                + carry as u16;
            (*result).set_digit(i, (sum % 256) as u8);
            carry = (sum / 256) as u8;
        }

        if carry > 0 {
            (*result).set_digit(max_size, carry);
        } else {
            (*result).meta = BigNum::encode_meta(max_size as u64, lhs_neg);
        }

        result
    }

    pub unsafe fn sub(
        lhs: *mut BigNum,
        rhs: *mut BigNum,
        gc: &mut GarbageCollector,
    ) -> *mut BigNum {
        let (lhs_size, lhs_neg) = (*lhs).decode_meta();
        let (rhs_size, rhs_neg) = (*rhs).decode_meta();

        if lhs_neg != rhs_neg {
            let temp = Self::add(lhs, rhs, gc);
            (*temp).set_negative(lhs_neg);
            return temp;
        }

        let (bigger, smaller, swapped) = Self::order_by_abs(lhs, rhs);
        let result_size = (*bigger).size() as usize;
        let result = gc.allocate_bignum(result_size as u64, swapped != lhs_neg);

        let mut borrow = 0i16;
        for i in 0..result_size {
            let mut diff = (*bigger).get_digit(i) as i16
                - (*smaller).get_digit(i) as i16
                - borrow;

            if diff < 0 {
                diff += 256;
                borrow = 1;
            } else {
                borrow = 0;
            }

            (*result).set_digit(i, diff as u8);
        }

        let mut actual_size = result_size;
        while actual_size > 1 && (*result).get_digit(actual_size - 1) == 0 {
            actual_size -= 1;
        }
        if actual_size != result_size {
            (*result).meta = BigNum::encode_meta(
                actual_size as u64,
                (*result).is_negative(),
            );
        }

        result
    }

    pub unsafe fn mul(
        lhs: *mut BigNum,
        rhs: *mut BigNum,
        gc: &mut GarbageCollector,
    ) -> *mut BigNum {
        let (lhs_size, lhs_neg) = (*lhs).decode_meta();
        let (rhs_size, rhs_neg) = (*rhs).decode_meta();

        let result_size = (lhs_size + rhs_size) as usize;
        let result_neg = lhs_neg != rhs_neg;

        let result = gc.allocate_bignum(result_size as u64, result_neg);
        Self::zero_digits((*result).digits(), result_size);

        for i in 0..lhs_size as usize {
            let mut carry = 0u16;
            for j in 0..rhs_size as usize {
                let prod = (*lhs).get_digit(i) as u16
                    * (*rhs).get_digit(j) as u16
                    + (*result).get_digit(i + j) as u16
                    + carry;

                (*result).set_digit(i + j, (prod % 256) as u8);
                carry = prod / 256;
            }

            if carry > 0 {
                (*result).set_digit(i + rhs_size as usize, carry as u8);
            }
        }

        let mut actual_size = result_size;
        while actual_size > 1 && (*result).get_digit(actual_size - 1) == 0 {
            actual_size -= 1;
        }
        if actual_size != result_size {
            (*result).meta =
                BigNum::encode_meta(actual_size as u64, result_neg);
        }

        result
    }

    pub unsafe fn div(
        lhs: *mut BigNum,
        rhs: *mut BigNum,
        gc: &mut GarbageCollector,
    ) -> *mut BigNum {
        let (lhs_size, lhs_neg) = (*lhs).decode_meta();
        let (rhs_size, rhs_neg) = (*rhs).decode_meta();

        assert!(rhs_size > 0, "Division by zero");

        if lhs_size < rhs_size
            || (lhs_size == rhs_size
                && (*lhs).get_digit(lhs_size as usize - 1)
                    < (*rhs).get_digit(rhs_size as usize - 1))
        {
            return gc.allocate_bignum(1, false); // Return zero
        }

        let result_size = lhs_size - rhs_size + 1;
        let result_neg = lhs_neg != rhs_neg;

        let result = gc.allocate_bignum(result_size, result_neg);
        let mut remainder = gc.allocate_bignum(lhs_size, lhs_neg);

        Self::copy_digits(
            (*lhs).digits(),
            (*remainder).digits(),
            lhs_size as usize,
        );

        for i in (0..=((lhs_size - rhs_size) as usize)).rev() {
            let mut q = ((*remainder).get_digit(i + rhs_size as usize - 1)
                as u16
                * 256
                + (*remainder).get_digit(i + rhs_size as usize - 2) as u16)
                / ((*rhs).get_digit(rhs_size as usize - 1) as u16 + 1);

            let mut borrow = 0i32;
            for j in 0..rhs_size as usize {
                let prod = q as i32 * (*rhs).get_digit(j) as i32;
                let diff = (*remainder).get_digit(i + j) as i32 - prod - borrow;
                if diff < 0 {
                    (*remainder).set_digit(i + j, (diff + 256) as u8);
                    borrow = 1;
                } else {
                    (*remainder).set_digit(i + j, diff as u8);
                    borrow = 0;
                }
            }

            (*result).set_digit(i as usize, q as u8);
        }

        let mut actual_size = result_size as usize;
        while actual_size > 1 && (*result).get_digit(actual_size - 1) == 0 {
            actual_size -= 1;
        }
        if actual_size != result_size as usize {
            (*result).meta =
                BigNum::encode_meta(actual_size as u64, result_neg);
        }

        result
    }

    pub unsafe fn modulo(
        lhs: *mut BigNum,
        rhs: *mut BigNum,
        gc: &mut GarbageCollector,
    ) -> *mut BigNum {
        let (lhs_size, lhs_neg) = (*lhs).decode_meta();
        let (rhs_size, rhs_neg) = (*rhs).decode_meta();

        assert!(rhs_size > 0, "Modulo by zero");

        if lhs_size < rhs_size
            || (lhs_size == rhs_size
                && (*lhs).get_digit(lhs_size as usize - 1)
                    < (*rhs).get_digit(rhs_size as usize - 1))
        {
            let result = gc.allocate_bignum(lhs_size, lhs_neg);
            Self::copy_digits(
                (*lhs).digits(),
                (*result).digits(),
                lhs_size as usize,
            );
            return result;
        }

        let mut remainder = gc.allocate_bignum(lhs_size, lhs_neg);

        Self::copy_digits(
            (*lhs).digits(),
            (*remainder).digits(),
            lhs_size as usize,
        );

        for i in (0..=(lhs_size - rhs_size) as usize).rev() {
            let mut q = ((*remainder).get_digit(i + rhs_size as usize - 1)
                as u16
                * 256
                + (*remainder).get_digit(i + rhs_size as usize - 2) as u16)
                / ((*rhs).get_digit(rhs_size as usize - 1) as u16 + 1);

            let mut borrow = 0i32;
            for j in 0..rhs_size as usize {
                let prod = q as i32 * (*rhs).get_digit(j) as i32;
                let diff = (*remainder).get_digit(i + j) as i32 - prod - borrow;
                if diff < 0 {
                    (*remainder).set_digit(i + j, (diff + 256) as u8);
                    borrow = 1;
                } else {
                    (*remainder).set_digit(i + j, diff as u8);
                    borrow = 0;
                }
            }
        }

        // Trim leading zeros
        let mut actual_size = lhs_size as usize;
        while actual_size > 1 && (*remainder).get_digit(actual_size - 1) == 0 {
            actual_size -= 1;
        }
        if actual_size != lhs_size as usize {
            (*remainder).meta =
                BigNum::encode_meta(actual_size as u64, lhs_neg);
        }

        remainder
    }

    pub unsafe fn bit_and(
        lhs: *mut BigNum,
        rhs: *mut BigNum,
        gc: &mut GarbageCollector,
    ) -> *mut BigNum {
        unimplemented!()
    }
    pub unsafe fn bit_or(
        lhs: *mut BigNum,
        rhs: *mut BigNum,
        gc: &mut GarbageCollector,
    ) -> *mut BigNum {
        unimplemented!()
    }
    pub unsafe fn bit_xor(
        lhs: *mut BigNum,
        rhs: *mut BigNum,
        gc: &mut GarbageCollector,
    ) -> *mut BigNum {
        unimplemented!()
    }
    pub unsafe fn bit_not(
        num: *mut BigNum,
        gc: &mut GarbageCollector,
    ) -> *mut BigNum {
        unimplemented!()
    }
    pub unsafe fn eq(lhs: *mut BigNum, rhs: *mut BigNum) -> bool {
        unimplemented!()
    }
    pub unsafe fn gt(lhs: *mut BigNum, rhs: *mut BigNum) -> bool {
        unimplemented!()
    }
    pub unsafe fn lt(lhs: *mut BigNum, rhs: *mut BigNum) -> bool {
        unimplemented!()
    }
    pub unsafe fn geq(lhs: *mut BigNum, rhs: *mut BigNum) -> bool {
        unimplemented!()
    }
    pub unsafe fn leq(lhs: *mut BigNum, rhs: *mut BigNum) -> bool {
        unimplemented!()
    }
    pub unsafe fn as_int(num: *mut BigNum) -> i64 {
        unimplemented!()
    }
    pub unsafe fn from_int(num: i64, gc: &mut GarbageCollector) -> *mut BigNum {
        unimplemented!()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_meta_encoding() {
        let test_cases = [
            (0, false),
            (1, false),
            (1 << 61, false),
            (42, true),
            ((1 << 62) - 1, true),
        ];

        for (size, negative) in test_cases {
            let meta = BigNum::encode_meta(size, negative);
            let bignum = BigNum {
                header: ObjectHeader::null(),
                meta,
            };
            let (decoded_size, decoded_negative) = bignum.decode_meta();
            assert_eq!(decoded_size, size, "size mismatch");
            assert_eq!(decoded_negative, negative, "sign mismatch");
        }
    }

    #[test]
    fn test_setters() {
        let mut bignum = BigNum {
            header: ObjectHeader::null(),
            meta: BigNum::encode_meta(42, false),
        };

        assert_eq!(bignum.size(), 42);
        assert_eq!(bignum.is_negative(), false);

        bignum.set_size(100);
        assert_eq!(bignum.size(), 100);
        assert_eq!(bignum.is_negative(), false);

        bignum.set_negative(true);
        assert_eq!(bignum.size(), 100);
        assert_eq!(bignum.is_negative(), true);
    }

    #[test]
    #[should_panic(expected = "size too large for BigNum")]
    fn test_size_too_large() {
        BigNum::encode_meta(1 << 62, false);
    }

    #[test]
    fn test_bignum_allocation() {
        let mut gc = GarbageCollector::new();
        gc.init_special_objects();

        unsafe {
            let num = gc.allocate_bignum(42, false);
            assert_eq!((*num).size(), 42);
            assert_eq!((*num).is_negative(), false);

            let neg_num = gc.allocate_bignum(100, true);
            assert_eq!((*neg_num).size(), 100);
            assert_eq!((*neg_num).is_negative(), true);
        }
    }

    #[test]
    fn test_basic_addition() {
        let mut gc = GarbageCollector::new();
        gc.init_special_objects();

        unsafe {
            let a = BigNum::from_bytes(&mut gc, &[1, 2], false); // 513 in base 256
            let b = BigNum::from_bytes(&mut gc, &[3, 1], false); // 259 in base 256

            let sum = BigNum::add(a, b, &mut gc);
            assert_eq!((*sum).get_digit(0), 4); // 772 = 513 + 259
            assert_eq!((*sum).get_digit(1), 3);
            assert_eq!((*sum).is_negative(), false);
        }
    }
    #[test]
    fn test_addition_with_carry() {
        let mut gc = GarbageCollector::new();
        gc.init_special_objects();

        unsafe {
            let a = BigNum::from_bytes(&mut gc, &[255], false);
            let b = BigNum::from_bytes(&mut gc, &[1], false);

            let sum = BigNum::add(a, b, &mut gc);
            assert_eq!((*sum).get_digit(0), 0);
            assert_eq!((*sum).get_digit(1), 1);
            assert_eq!((*sum).size(), 2);
        }
    }

    #[test]
    fn test_subtraction() {
        let mut gc = GarbageCollector::new();
        gc.init_special_objects();

        unsafe {
            let a = BigNum::from_bytes(&mut gc, &[3, 1], false); // 259
            let b = BigNum::from_bytes(&mut gc, &[1], false); // 1

            let diff = BigNum::sub(a, b, &mut gc);
            assert_eq!((*diff).get_digit(0), 2); // 258 = 259 - 1
            assert_eq!((*diff).get_digit(1), 1);
            assert_eq!((*diff).is_negative(), false);
        }
    }

    #[test]
    fn test_sign_switch_subtraction() {
        let mut gc = GarbageCollector::new();
        gc.init_special_objects();

        // unsafe {
        // // Case 1: larger - smaller = positive
        // let a = BigNum::from_bytes(&mut gc, &[10], false); // 10
        // let b = BigNum::from_bytes(&mut gc, &[3], false); // 3
        // let diff = BigNum::sub(a, b, &mut gc);
        // assert_eq!((*diff).get_digit(0), 7);
        // assert_eq!((*diff).is_negative(), false); // 10 - 3 = 7
        //
        // // Case 2: smaller - larger = negative
        // let a = BigNum::from_bytes(&mut gc, &[3], false); // 3
        // let b = BigNum::from_bytes(&mut gc, &[10], false); // 10
        // let diff = BigNum::sub(a, b, &mut gc);
        // assert_eq!((*diff).get_digit(0), 7);
        // assert_eq!((*diff).is_negative(), true); // 3 - 10 = -7
        //
        // // Case 3: negative - negative, |a| > |b|
        // let a = BigNum::from_bytes(&mut gc, &[10], true); // -10
        // let b = BigNum::from_bytes(&mut gc, &[3], true); // -3
        // let diff = BigNum::sub(a, b, &mut gc);
        // assert_eq!((*diff).get_digit(0), 7);
        // assert_eq!((*diff).is_negative(), true); // -10 - (-3) = -7
        //
        // // Case 4: negative - negative, |a| < |b|
        // let a = BigNum::from_bytes(&mut gc, &[3], true); // -3
        // let b = BigNum::from_bytes(&mut gc, &[10], true); // -10
        // let diff = BigNum::sub(a, b, &mut gc);
        // assert_eq!((*diff).get_digit(0), 7);
        // assert_eq!((*diff).is_negative(), false); // -3 - (-10) = 7
        //
        // // Case 5: positive - negative
        // let a = BigNum::from_bytes(&mut gc, &[3], false); // 3
        // let b = BigNum::from_bytes(&mut gc, &[4], true); // -4
        // let diff = BigNum::sub(a, b, &mut gc);
        // assert_eq!((*diff).get_digit(0), 7);
        // assert_eq!((*diff).is_negative(), false); // 3 - (-4) = 7
        //
        // // Case 6: negative - positive
        // let a = BigNum::from_bytes(&mut gc, &[3], true); // -3
        // let b = BigNum::from_bytes(&mut gc, &[4], false); // 4
        // let diff = BigNum::sub(a, b, &mut gc);
        // assert_eq!((*diff).get_digit(0), 7);
        // assert_eq!((*diff).is_negative(), true); // -3 - 4 = -7
        // }
    }

    #[test]
    fn test_sign_rules_multiplication() {
        let mut gc = GarbageCollector::new();
        gc.init_special_objects();

        unsafe {
            // Case 1: positive * positive = positive
            let a = BigNum::from_bytes(&mut gc, &[2], false); // 2
            let b = BigNum::from_bytes(&mut gc, &[3], false); // 3
            let prod = BigNum::mul(a, b, &mut gc);
            assert_eq!((*prod).get_digit(0), 6);
            assert_eq!((*prod).is_negative(), false); // 2 * 3 = 6

            // Case 2: positive * negative = negative
            let a = BigNum::from_bytes(&mut gc, &[2], false); // 2
            let b = BigNum::from_bytes(&mut gc, &[3], true); // -3
            let prod = BigNum::mul(a, b, &mut gc);
            assert_eq!((*prod).get_digit(0), 6);
            assert_eq!((*prod).is_negative(), true); // 2 * (-3) = -6

            // Case 3: negative * positive = negative
            let a = BigNum::from_bytes(&mut gc, &[2], true); // -2
            let b = BigNum::from_bytes(&mut gc, &[3], false); // 3
            let prod = BigNum::mul(a, b, &mut gc);
            assert_eq!((*prod).get_digit(0), 6);
            assert_eq!((*prod).is_negative(), true); // -2 * 3 = -6

            // Case 4: negative * negative = positive
            let a = BigNum::from_bytes(&mut gc, &[2], true); // -2
            let b = BigNum::from_bytes(&mut gc, &[3], true); // -3
            let prod = BigNum::mul(a, b, &mut gc);
            assert_eq!((*prod).get_digit(0), 6);
            assert_eq!((*prod).is_negative(), false); // -2 * (-3) = 6

            // Case 5: multiplication by large numbers preserves sign rules
            let a = BigNum::from_bytes(&mut gc, &[0xFF, 0xFF], true); // -65535
            let b = BigNum::from_bytes(&mut gc, &[0xFF, 0xFF], true); // -65535
            let prod = BigNum::mul(a, b, &mut gc);
            assert_eq!((*prod).is_negative(), false); // negative * negative = positive
        }
    }

    #[test]
    fn test_division() {
        let mut gc = GarbageCollector::new();
        gc.init_special_objects();

        // unsafe {
        // Simple division
        // let a = BigNum::from_bytes(&mut gc, &[6], false); // 6
        // let b = BigNum::from_bytes(&mut gc, &[2], false); // 2
        // let quot = BigNum::div(a, b, &mut gc);
        // assert_eq!((*quot).get_digit(0), 3); // 3 = 6 / 2
        // assert_eq!((*quot).size(), 1);
        // assert_eq!((*quot).is_negative(), false);

        // // Division with remainder
        // let a = BigNum::from_bytes(&mut gc, &[7], false); // 7
        // let b = BigNum::from_bytes(&mut gc, &[2], false); // 2
        // let quot = BigNum::div(a, b, &mut gc);
        // assert_eq!((*quot).get_digit(0), 3); // 3 = floor(7 / 2)
        //
        // // Multi-byte division
        // let a = BigNum::from_bytes(&mut gc, &[0x00, 0x01], false); // 256
        // let b = BigNum::from_bytes(&mut gc, &[0x02], false); // 2
        // let quot = BigNum::div(a, b, &mut gc);
        // assert_eq!((*quot).get_digit(0), 0x80); // 128 = 256 / 2
        // assert_eq!((*quot).size(), 1);
        //
        // // Division by larger number
        // let a = BigNum::from_bytes(&mut gc, &[2], false); // 2
        // let b = BigNum::from_bytes(&mut gc, &[3], false); // 3
        // let quot = BigNum::div(a, b, &mut gc);
        // assert_eq!((*quot).get_digit(0), 0); // 0 = floor(2 / 3)
        // assert_eq!((*quot).size(), 1);
        //
        // // Test sign rules
        // let a = BigNum::from_bytes(&mut gc, &[6], true); // -6
        // let b = BigNum::from_bytes(&mut gc, &[2], false); // 2
        // let quot = BigNum::div(a, b, &mut gc);
        // assert_eq!((*quot).get_digit(0), 3);
        // assert_eq!((*quot).is_negative(), true); // -3 = -6 / 2
        //
        // let a = BigNum::from_bytes(&mut gc, &[6], true); // -6
        // let b = BigNum::from_bytes(&mut gc, &[2], true); // -2
        // let quot = BigNum::div(a, b, &mut gc);
        // assert_eq!((*quot).get_digit(0), 3);
        // assert_eq!((*quot).is_negative(), false); // 3 = -6 / -2
        // }
    }

    #[test]
    #[should_panic]
    fn test_division_by_zero() {
        let mut gc = GarbageCollector::new();
        gc.init_special_objects();

        unsafe {
            let num = BigNum::from_bytes(&mut gc, &[42], false); // 42
            let zero = BigNum::from_bytes(&mut gc, &[0], false); // 0
            BigNum::div(num, zero, &mut gc); // Should panic
        }
    }

    #[test]
    #[should_panic]
    fn test_modulo_by_zero() {
        let mut gc = GarbageCollector::new();
        gc.init_special_objects();

        unsafe {
            let num = BigNum::from_bytes(&mut gc, &[42], false); // 42
            let zero = BigNum::from_bytes(&mut gc, &[0], false); // 0
            BigNum::modulo(num, zero, &mut gc); // Should panic
        }
    }
}
