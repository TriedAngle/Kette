use core::fmt;
use core::marker::PhantomData;
use core::num::NonZeroUsize;
use core::ptr::NonNull;
use std::ops::{Add, AddAssign, Sub, SubAssign};

use crate::ValueTag;

// TODO: this is currently not the greatest and logical system
// I think at the end I should have the following:
// Value: any `object`, ptr or small int
// Tagged<T: Value>: still like value but typed
// Handle<T: HeapObject>: any heap located object
//
// Tagged<T> would replace most of current tagging system.
// Handle<T> would represent a heap object that we KNOW is GC safe (we root them)
// we can implement safe deref for Handle<T> and some unsafe deref for Tagged

#[repr(transparent)]
#[derive(Copy, Clone, Hash)]
pub struct TaggedPtr<T> {
    raw: NonZeroUsize,
    _marker: PhantomData<T>,
}

impl<T> TaggedPtr<T> {
    const TAG_MASK: usize = 0b11;
    const REF_TAG: usize = ValueTag::Reference as usize;

    #[inline]
    pub fn from_nonnull(nn: NonNull<T>) -> Self {
        let addr = nn.as_ptr() as usize;
        debug_assert_eq!(
            addr & Self::TAG_MASK,
            0,
            "pointer must be aligned so low 2 bits are free"
        );
        let tagged = addr | Self::REF_TAG;
        let raw = NonZeroUsize::new(tagged).expect("tagged pointer must be non-zero");
        Self {
            raw,
            _marker: PhantomData,
        }
    }

    /// Create from &T.
    #[inline]
    pub fn from_ref(r: &T) -> Self {
        let nn = NonNull::from(r);
        Self::from_nonnull(nn)
    }

    /// Create from &mut T.
    #[inline]
    pub fn from_mut(r: &mut T) -> Self {
        let nn = NonNull::from(r);
        Self::from_nonnull(nn)
    }

    /// Returns the raw tagged integer.
    #[inline]
    pub fn into_raw(self) -> NonZeroUsize {
        self.raw
    }

    /// Rebuild from a raw tagged integer (must be a Reference-tagged pointer).
    #[inline]
    pub fn from_raw(raw: NonZeroUsize) -> Option<Self> {
        if raw.get() & Self::TAG_MASK == Self::REF_TAG {
            Some(Self {
                raw,
                _marker: PhantomData,
            })
        } else {
            None
        }
    }

    /// Returns true iff the value is a reference-tagged pointer.
    #[inline]
    pub fn is_reference_tag(self) -> bool {
        (self.raw.get() & Self::TAG_MASK) == Self::REF_TAG
    }

    /// Strip the tag and return as NonNull<T>.
    #[inline]
    pub fn to_nonnull(self) -> NonNull<T> {
        // SAFETY: we always set REF_TAG, so low bits != 0; stripping them yields original NonNull.
        let addr = (self.raw.get() & !Self::TAG_MASK) as *mut T;
        // SAFETY: construction guarantees non-null.
        unsafe { NonNull::new_unchecked(addr) }
    }

    /// Get a const pointer to T (tag stripped).
    #[inline]
    pub fn as_ptr(self) -> *const T {
        self.to_nonnull().as_ptr() as *const T
    }

    /// Get a mut pointer to T (tag stripped).
    #[inline]
    pub fn as_mut_ptr(self) -> *mut T {
        self.to_nonnull().as_ptr()
    }

    /// # Safety
    /// Caller must ensure the pointed-to value is valid for shared borrows.
    #[inline]
    pub unsafe fn as_ref<'a>(self) -> &'a T {
        unsafe { &*self.as_ptr() }
    }

    /// # Safety
    /// Caller must ensure unique access and validity for mutable borrows.
    #[inline]
    pub unsafe fn as_mut<'a>(self) -> &'a mut T {
        unsafe { &mut *self.as_mut_ptr() }
    }

    pub unsafe fn cast<U>(self) -> TaggedPtr<U> {
        unsafe { std::mem::transmute(self) }
    }
}

impl<T> fmt::Debug for TaggedPtr<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("TaggedPtr")
            .field(&format_args!("0x{:x}", self.raw.get()))
            .finish()
    }
}

impl<T> PartialEq for TaggedPtr<T> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.raw.get() == other.raw.get()
    }
}
impl<T> Eq for TaggedPtr<T> {}

#[repr(transparent)]
#[derive(Copy, Clone, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TaggedI64(i64);

#[repr(transparent)]
#[derive(Copy, Clone, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TaggedU64(u64);

#[repr(transparent)]
#[derive(Copy, Clone, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TaggedUsize(usize);

impl fmt::Debug for TaggedI64 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "TaggedI64({})", self.to_i64())
    }
}
impl fmt::Debug for TaggedU64 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "TaggedU64({})", self.to_u64())
    }
}
impl fmt::Debug for TaggedUsize {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "TaggedUsize({})", self.to_usize())
    }
}

impl TaggedI64 {
    #[inline]
    pub fn new(v: i64) -> Self {
        Self(v.wrapping_shl(1))
    }
    #[inline]
    pub fn from_raw_tagged(raw: i64) -> Self {
        debug_assert_eq!(raw & 1, 0);
        Self(raw)
    }
    #[inline]
    pub fn raw(self) -> i64 {
        self.0
    }
    #[inline]
    pub fn to_i64(self) -> i64 {
        self.0 >> 1
    }
    #[inline]
    pub fn is_small_int(self) -> bool {
        (self.0 & 1) == 0
    }
}
impl From<i64> for TaggedI64 {
    #[inline]
    fn from(v: i64) -> Self {
        Self::new(v)
    }
}
impl From<TaggedI64> for i64 {
    #[inline]
    fn from(t: TaggedI64) -> i64 {
        t.to_i64()
    }
}

impl TaggedU64 {
    #[inline]
    pub fn new(v: u64) -> Self {
        Self(v << 1)
    }
    #[inline]
    pub fn from_raw_tagged(raw: u64) -> Self {
        debug_assert_eq!(raw & 1, 0);
        Self(raw)
    }
    #[inline]
    pub fn raw(self) -> u64 {
        self.0
    }
    #[inline]
    pub fn to_u64(self) -> u64 {
        self.0 >> 1
    }
    #[inline]
    pub fn is_small_int(self) -> bool {
        (self.0 & 1) == 0
    }
}
impl From<u64> for TaggedU64 {
    #[inline]
    fn from(v: u64) -> Self {
        Self::new(v)
    }
}
impl From<TaggedU64> for u64 {
    #[inline]
    fn from(t: TaggedU64) -> u64 {
        t.to_u64()
    }
}

impl TaggedUsize {
    #[inline]
    pub fn new(v: usize) -> Self {
        Self(v << 1)
    }
    #[inline]
    pub fn from_raw_tagged(raw: usize) -> Self {
        debug_assert_eq!(raw & 1, 0);
        Self(raw)
    }
    #[inline]
    pub fn raw(self) -> usize {
        self.0
    }
    #[inline]
    pub fn to_usize(self) -> usize {
        self.0 >> 1
    } // logical shift
    #[inline]
    pub fn is_small_int(self) -> bool {
        (self.0 & 1) == 0
    }
}
impl From<usize> for TaggedUsize {
    #[inline]
    fn from(v: usize) -> Self {
        Self::new(v)
    }
}
impl From<TaggedUsize> for usize {
    #[inline]
    fn from(t: TaggedUsize) -> usize {
        t.to_usize()
    }
}

/// ----- Arithmetic on *tagged* values (no shifting needed) -----
/// Properties:
///   (a<<1) + (b<<1) = (a+b)<<1
///   (a<<1) - (b<<1) = (a-b)<<1
impl Add for TaggedI64 {
    type Output = Self;
    #[inline]
    fn add(self, rhs: Self) -> Self::Output {
        Self(self.0.wrapping_add(rhs.0))
    }
}
impl Sub for TaggedI64 {
    type Output = Self;
    #[inline]
    fn sub(self, rhs: Self) -> Self::Output {
        Self(self.0.wrapping_sub(rhs.0))
    }
}
impl AddAssign for TaggedI64 {
    #[inline]
    fn add_assign(&mut self, rhs: Self) {
        self.0 = self.0.wrapping_add(rhs.0)
    }
}
impl SubAssign for TaggedI64 {
    #[inline]
    fn sub_assign(&mut self, rhs: Self) {
        self.0 = self.0.wrapping_sub(rhs.0)
    }
}

impl Add for TaggedU64 {
    type Output = Self;
    #[inline]
    fn add(self, rhs: Self) -> Self::Output {
        Self(self.0.wrapping_add(rhs.0))
    }
}
impl Sub for TaggedU64 {
    type Output = Self;
    #[inline]
    fn sub(self, rhs: Self) -> Self::Output {
        Self(self.0.wrapping_sub(rhs.0))
    }
}
impl AddAssign for TaggedU64 {
    #[inline]
    fn add_assign(&mut self, rhs: Self) {
        self.0 = self.0.wrapping_add(rhs.0)
    }
}
impl SubAssign for TaggedU64 {
    #[inline]
    fn sub_assign(&mut self, rhs: Self) {
        self.0 = self.0.wrapping_sub(rhs.0)
    }
}

impl Add for TaggedUsize {
    type Output = Self;
    #[inline]
    fn add(self, rhs: Self) -> Self::Output {
        Self(self.0.wrapping_add(rhs.0))
    }
}
impl Sub for TaggedUsize {
    type Output = Self;
    #[inline]
    fn sub(self, rhs: Self) -> Self::Output {
        Self(self.0.wrapping_sub(rhs.0))
    }
}
impl AddAssign for TaggedUsize {
    #[inline]
    fn add_assign(&mut self, rhs: Self) {
        self.0 = self.0.wrapping_add(rhs.0)
    }
}
impl SubAssign for TaggedUsize {
    #[inline]
    fn sub_assign(&mut self, rhs: Self) {
        self.0 = self.0.wrapping_sub(rhs.0)
    }
}

impl Add<i64> for TaggedI64 {
    type Output = Self;
    #[inline]
    fn add(self, rhs: i64) -> Self::Output {
        self + TaggedI64::new(rhs)
    }
}
impl Sub<i64> for TaggedI64 {
    type Output = Self;
    #[inline]
    fn sub(self, rhs: i64) -> Self::Output {
        self - TaggedI64::new(rhs)
    }
}
impl Add<u64> for TaggedU64 {
    type Output = Self;
    #[inline]
    fn add(self, rhs: u64) -> Self::Output {
        self + TaggedU64::new(rhs)
    }
}
impl Sub<u64> for TaggedU64 {
    type Output = Self;
    #[inline]
    fn sub(self, rhs: u64) -> Self::Output {
        self - TaggedU64::new(rhs)
    }
}
impl Add<usize> for TaggedUsize {
    type Output = Self;
    #[inline]
    fn add(self, rhs: usize) -> Self::Output {
        self + TaggedUsize::new(rhs)
    }
}
impl Sub<usize> for TaggedUsize {
    type Output = Self;
    #[inline]
    fn sub(self, rhs: usize) -> Self::Output {
        self - TaggedUsize::new(rhs)
    }
}

#[repr(transparent)]
#[derive(Copy, Clone, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TaggedValue(u64);

impl fmt::Debug for TaggedValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let kind = if self.is_reference() {
            "Ref"
        } else if self.is_header() {
            "Header"
        } else {
            "SmallInt"
        };
        write!(f, "TaggedValue(0x{:016x}, {})", self.0, kind)
    }
}

impl TaggedValue {
    const TAG_MASK: u64 = 0b11;
    const INT_TAG: u64 = ValueTag::Integer as u64;
    const REF_TAG: u64 = ValueTag::Reference as u64;
    const HDR_TAG: u64 = ValueTag::Header as u64;

    #[inline]
    pub fn raw(self) -> u64 {
        self.0
    }

    #[inline]
    pub fn zero() -> Self {
        Self(0)
    }

    #[inline]
    pub fn is_small_int(self) -> bool {
        (self.0 & 1) == Self::INT_TAG
    }
    #[inline]
    pub fn is_reference(self) -> bool {
        (self.0 & Self::TAG_MASK) == Self::REF_TAG
    }
    #[inline]
    pub fn is_header(self) -> bool {
        (self.0 & Self::TAG_MASK) == Self::HDR_TAG
    }

    #[inline]
    pub fn from_small_i64(v: i64) -> Self {
        TaggedI64::new(v).into()
    }
    #[inline]
    pub fn from_small_u64(v: u64) -> Self {
        TaggedU64::new(v).into()
    }
    #[inline]
    pub fn from_small_usize(v: usize) -> Self {
        TaggedUsize::new(v).into()
    }

    #[inline]
    pub fn as_reference<T>(self) -> Option<TaggedPtr<T>> {
        if self.is_reference() {
            return Some(TaggedPtr::from(self));
        }
        None
    }
}

impl From<TaggedI64> for TaggedValue {
    #[inline]
    fn from(t: TaggedI64) -> Self {
        TaggedValue(t.raw().cast_unsigned())
    }
}
impl From<TaggedU64> for TaggedValue {
    #[inline]
    fn from(t: TaggedU64) -> Self {
        TaggedValue(t.raw())
    }
}
impl From<TaggedUsize> for TaggedValue {
    #[inline]
    fn from(t: TaggedUsize) -> Self {
        TaggedValue(t.raw() as u64)
    }
}

impl From<TaggedValue> for TaggedI64 {
    #[inline]
    fn from(v: TaggedValue) -> Self {
        TaggedI64::from_raw_tagged(v.0.cast_signed())
    }
}
impl From<TaggedValue> for TaggedU64 {
    #[inline]
    fn from(v: TaggedValue) -> Self {
        TaggedU64::from_raw_tagged(v.0)
    }
}
impl From<TaggedValue> for TaggedUsize {
    #[inline]
    fn from(v: TaggedValue) -> Self {
        TaggedUsize::from_raw_tagged(v.0 as usize)
    }
}

impl<T> From<TaggedPtr<T>> for TaggedValue {
    #[inline]
    fn from(p: TaggedPtr<T>) -> Self {
        TaggedValue(p.into_raw().get() as u64)
    }
}

impl<T> From<TaggedValue> for TaggedPtr<T> {
    #[inline]
    fn from(v: TaggedValue) -> Self {
        assert!(
            v.0 & TaggedValue::TAG_MASK == TaggedValue::REF_TAG,
            "value is not a reference"
        );
        let usize_val: usize = v.0 as usize;
        let raw = NonZeroUsize::new(usize_val).expect("this shouldn't occour");
        TaggedPtr::from_raw(raw).expect("this shouldn't occour neither")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use core::mem;

    // Helper: pick unsigned values that won't overflow when left-shifted by 1.
    fn good_u64_values() -> [u64; 6] {
        [
            0,
            1,
            42,
            (1u64 << 40),
            (1u64 << 62) - 1, // top bit remains 0
            (1u64 << 63) - 1, // still safe (highest bit 0)
        ]
    }
    fn good_usize_values() -> Vec<usize> {
        let bits = usize::BITS as usize;
        let max_safe = if bits >= 2 {
            (1usize << (bits - 1)) - 1
        } else {
            0
        };
        vec![0, 1, 12345, 1 << (bits.saturating_sub(3)), max_safe]
    }
    fn good_i64_values() -> [i64; 8] {
        [
            0,
            1,
            -1,
            42,
            -42,
            (1i64 << 40),
            -((1i64 << 40) - 1),
            (1i64 << 62) - 1, // keep sign bit 0 to avoid overflow on <<1
        ]
    }

    #[test]
    fn tagged_i64_roundtrip_and_flags() {
        for &v in &good_i64_values() {
            let t = TaggedI64::new(v);
            assert!(t.is_small_int(), "TaggedI64 should set small-int tag");
            assert_eq!(t.to_i64(), v, "i64 roundtrip failed for {v}");
            // via TaggedValue
            let tv: TaggedValue = t.into();
            assert!(
                tv.is_small_int(),
                "TaggedValue should be small-int from i64"
            );
            let back: TaggedI64 = tv.into();
            assert_eq!(
                back.to_i64(),
                v,
                "TaggedValue<i64> roundtrip failed for {v}"
            );
        }
    }

    #[test]
    fn tagged_u64_roundtrip_and_flags() {
        for &v in &good_u64_values() {
            let t = TaggedU64::new(v);
            assert!(t.is_small_int(), "TaggedU64 should set small-int tag");
            assert_eq!(t.to_u64(), v, "u64 roundtrip failed for {v}");
            // via TaggedValue
            let tv: TaggedValue = t.into();
            assert!(
                tv.is_small_int(),
                "TaggedValue should be small-int from u64: {:?}",
                v
            );
            let back: TaggedU64 = tv.into();
            assert_eq!(
                back.to_u64(),
                v,
                "TaggedValue<u64> roundtrip failed for {v}"
            );
        }
    }

    #[test]
    fn tagged_usize_roundtrip_and_flags() {
        for &v in &good_usize_values() {
            let t = TaggedUsize::new(v);
            assert!(t.is_small_int(), "TaggedUsize should set small-int tag");
            assert_eq!(t.to_usize(), v, "usize roundtrip failed for {v}");
            // via TaggedValue
            let tv: TaggedValue = t.into();
            assert!(
                tv.is_small_int(),
                "TaggedValue should be small-int from usize"
            );
            let back: TaggedUsize = tv.into();
            assert_eq!(
                back.to_usize(),
                v,
                "TaggedValue<usize> roundtrip failed for {v}"
            );
        }
    }

    #[test]
    fn taggedvalue_constructors_helpers_work() {
        // i64
        for &v in &good_i64_values() {
            let tv = TaggedValue::from_small_i64(v);
            assert!(tv.is_small_int());
            let back: TaggedI64 = tv.into();
            assert_eq!(back.to_i64(), v);
        }
        // u64
        for &v in &good_u64_values() {
            let tv = TaggedValue::from_small_u64(v);
            assert!(tv.is_small_int());
            let back: TaggedU64 = tv.into();
            assert_eq!(back.to_u64(), v);
        }
        // usize
        for &v in &good_usize_values() {
            let tv = TaggedValue::from_small_usize(v);
            assert!(tv.is_small_int());
            let back: TaggedUsize = tv.into();
            assert_eq!(back.to_usize(), v);
        }
    }

    #[test]
    fn taggedptr_from_ref_and_back() {
        // Use u64 for alignment >= 4 so low 2 bits are free.
        let mut x: u64 = 0xDEADBEEF;
        let p_from_ref = TaggedPtr::<u64>::from_ref(&x);
        assert!(
            p_from_ref.is_reference_tag(),
            "Pointer should carry REF tag"
        );
        // as_ptr should equal the original address once stripped
        assert_eq!(p_from_ref.as_ptr(), &x as *const u64);

        let p_from_mut = TaggedPtr::<u64>::from_mut(&mut x);
        assert!(p_from_mut.is_reference_tag());
        assert_eq!(p_from_mut.as_mut_ptr(), &mut x as *mut u64);

        // into_raw / from_raw
        let raw = p_from_ref.into_raw();
        let rebuilt = TaggedPtr::<u64>::from_raw(raw).expect("should be reference-tagged");
        assert_eq!(rebuilt.as_ptr(), &x as *const u64);

        // NonNull roundtrip
        let nn = NonNull::from(&mut x);
        let p_from_nn = TaggedPtr::<u64>::from_nonnull(nn);
        assert_eq!(p_from_nn.to_nonnull().as_ptr(), nn.as_ptr());
    }

    #[test]
    fn taggedptr_to_from_taggedvalue() {
        let mut x: u64 = 123456789;
        let p = TaggedPtr::<u64>::from_mut(&mut x);

        // TaggedPtr<T> -> TaggedValue
        let tv: TaggedValue = p.into();
        assert!(tv.is_reference(), "TaggedValue should be reference-tagged");

        // TaggedValue -> TaggedPtr<T> (same T)
        let p2: TaggedPtr<u64> = tv.into();
        assert_eq!(p2.as_mut_ptr(), &mut x as *mut u64);

        // Cross-qualify: TaggedPtr<U> via qualify
        // Safety: we're only reinterpreting the phantom type parameter for the test.
        let p_u32: TaggedPtr<u32> = unsafe { p2.cast::<u32>() };
        // Addresses should match; we're not dereferencing as u32.
        assert_eq!(p_u32.as_ptr() as *const u8, (&x as *const u64) as *const u8);
    }

    #[test]
    fn debug_impls_are_sensible() {
        // Smoke-test Debug formatting doesn't panic and mentions kind bits.
        let t_i = TaggedI64::new(7);
        let t_u = TaggedU64::new(7);
        let t_us = TaggedUsize::new(7);
        let dv_i: TaggedValue = t_i.into();
        let dv_u: TaggedValue = t_u.into();
        let dv_us: TaggedValue = t_us.into();
        let _ = format!("{t_i:?}");
        let _ = format!("{t_u:?}");
        let _ = format!("{t_us:?}");
        let s_i = format!("{dv_i:?}");
        let s_u = format!("{dv_u:?}");
        let s_us = format!("{dv_us:?}");
        assert!(s_i.contains("SmallInt"));
        assert!(s_u.contains("SmallInt"));
        assert!(s_us.contains("SmallInt"));

        // TaggedPtr Debug includes hex-ish raw
        let mut x: u64 = 1;
        let p = TaggedPtr::from_mut(&mut x);
        let s = format!("{p:?}");
        assert!(s.starts_with("TaggedPtr("));
        assert!(s.contains("0x"));
    }

    #[test]
    fn ptr_alignment_assumption_holds_for_test_type() {
        // Ensure our chosen pointer type meets the "low 2 bits free" debug assertion.
        assert!(
            mem::align_of::<u64>() >= 4,
            "u64 alignment should free low 2 bits"
        );
    }
}
