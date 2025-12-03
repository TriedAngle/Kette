//! Value: any raw value, small integer/reference/header
//!
//! Tagged<T>: same as Value but but typed (= type safe) for easier rust side type declaration, but not
//! safe to use
//!
//! Handle<T>: untagged value, small integer or reference, is safe to use, GC does not clear/move this
//! also implements Deref and DerefMut
use std::{
    marker::PhantomData,
    ops::{Deref, DerefMut},
};

use crate::{
    HeapObject, HeapValue, LookupResult, Object, PtrSizedObject, Selector, Visitable, VisitedLink,
};

#[allow(unused)]
#[repr(u8)]
#[derive(Debug, Copy, Clone)]
pub enum ValueTag {
    Fixnum = 0b0,
    Reference = 0b01,
    Header = 0b11,
}

pub const OBECT_TAG_MASK: u64 = 0b11;

/// A generic Value
#[repr(transparent)]
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct Value(u64);

/// A tagged value
/// same memory layout as Value but Typed
#[derive(Debug)]
pub struct Tagged<T: Object> {
    data: u64,
    _marker: PhantomData<*mut T>,
}

/// GC safe Reference to a HeapObject or an SMI
#[derive(Debug)]
pub struct Handle<T: Object> {
    data: u64,
    _marker: PhantomData<*mut T>,
}

unsafe impl Send for Value {}
unsafe impl Sync for Value {}

unsafe impl<T: Object> Send for Tagged<T> {}
unsafe impl<T: Object> Sync for Tagged<T> {}

unsafe impl<T: Object> Send for Handle<T> {}
unsafe impl<T: Object> Sync for Handle<T> {}

// we need custom clone implementation as default considers "owning" T
// but this represents a pointer to a T, not T itself
impl<T: Object> Clone for Tagged<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T: Object> Copy for Tagged<T> {}

impl<T: Object> Clone for Handle<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T: Object> Copy for Handle<T> {}

impl Value {
    pub fn from_fixnum(value: i64) -> Self {
        let casted = value.cast_unsigned();
        let tagged = casted << 1;
        Self(tagged)
    }

    pub fn from_u64(value: u64) -> Self {
        let tagged = value << 1;
        Self(tagged)
    }

    pub fn from_usize(value: usize) -> Self {
        Self::from_u64(value as u64)
    }

    pub fn zero() -> Self {
        Self::from_u64(0)
    }

    pub fn is_fixnum(&self) -> bool {
        self.0 & 0b1 == ValueTag::Fixnum as u64
    }

    pub fn is_object(&self) -> bool {
        self.0 & OBECT_TAG_MASK == ValueTag::Reference as u64
    }

    pub fn is_header(&self) -> bool {
        self.0 & OBECT_TAG_MASK == ValueTag::Header as u64
    }

    pub fn as_tagged_fixnum<T: PtrSizedObject>(self) -> Option<Tagged<T>> {
        if self.is_fixnum() {
            // SAFETY: we tested this
            let tagged = unsafe { Tagged::new_raw(self.0) };
            return Some(tagged);
        }
        None
    }

    pub fn as_tagged_object<T: HeapObject>(self) -> Option<Tagged<T>> {
        if self.is_object() {
            // SAFETY: we tested this
            let tagged = unsafe { Tagged::new_raw(self.0) };
            return Some(tagged);
        }
        None
    }

    /// # Safety
    /// check if this is a heap object
    pub unsafe fn as_tagged_object_unchecked<T: HeapObject>(self) -> Tagged<T> {
        // Safety: by contract this is a T
        unsafe { Tagged::new_raw(self.0) }
    }

    /// Create a handle from a value
    /// # Safety
    /// Caller must make sure Value doesn't get allocated
    pub unsafe fn as_handle_unchecked(self) -> Handle<Value> {
        Handle {
            data: self.0,
            _marker: PhantomData,
        }
    }

    /// Create a handle from a value
    /// # Safety
    /// Caller must make sure Value doesn't get allocated
    pub unsafe fn as_heap_handle_unchecked(self) -> Handle<HeapValue> {
        Handle {
            data: self.0,
            _marker: PhantomData,
        }
    }
}

impl<T: Object> Tagged<T> {
    #[inline]
    const unsafe fn new_raw(value: u64) -> Self {
        Self {
            data: value,
            _marker: PhantomData,
        }
    }

    #[inline]
    pub fn as_value(&self) -> Value {
        Value(self.data)
    }
}

impl<T: PtrSizedObject> Tagged<T> {
    #[inline]
    pub fn new_value(value: T) -> Self {
        let value = value.to_ptr_sized();
        let tagged = value << 1;
        unsafe { Self::new_raw(tagged) }
    }

    #[inline]
    pub fn raw(self) -> u64 {
        self.data
    }

    pub fn restore_u64(self) -> u64 {
        self.data >> 1
    }

    pub fn from_raw(value: T) -> Self {
        Self {
            data: value.to_ptr_sized(),
            _marker: PhantomData,
        }
    }
}

impl<T: HeapObject> Tagged<T> {
    #[inline]
    pub fn new_ptr(ptr: *mut T) -> Self {
        let value = ptr as u64;
        debug_assert_eq!(
            value & OBECT_TAG_MASK,
            0,
            "pointer must be aligned so low 2 bits are free"
        );
        let tagged = value | (ValueTag::Reference as u64);
        unsafe { Self::new_raw(tagged) }
    }

    #[inline]
    pub fn as_ptr(self) -> *mut T {
        let untagged = self.data & !(ValueTag::Reference as u64);
        untagged as _
    }

    /// Get a reference to a T
    /// # Safety
    /// this is overall not safe as we do not guarantee GC invocations inbetween.
    /// please consider using Handle<T> deref
    #[inline]
    pub unsafe fn as_ref<'a>(self) -> &'a T {
        debug_assert_eq!(
            self.data & OBECT_TAG_MASK,
            ValueTag::Reference as u64,
            "Tagged is not a valid pointer"
        );
        let untagged = self.data & !(ValueTag::Reference as u64);
        let ptr = untagged as *const T;
        // SAFETY: we did a check, but this is still not safe as GC can kill this
        unsafe { &*ptr }
    }

    /// Get a mutable reference to a T
    /// # Safety
    /// this is overall not safe as we do not guarantee GC invocations inbetween.
    /// please consider using Handle<T> deref mut
    #[inline]
    pub unsafe fn as_mut<'a>(self) -> &'a mut T {
        debug_assert_eq!(
            self.data & OBECT_TAG_MASK,
            ValueTag::Reference as u64,
            "Tagged is not a valid pointer"
        );
        let untagged = self.data & !(ValueTag::Reference as u64);
        let ptr = untagged as *mut T;
        // SAFETY: we did a check, but this is still not safe as GC can kill this
        unsafe { &mut *ptr }
    }

    /// promote Tagged<T> to a Handle<T>
    /// # Safety
    /// the GC must be made aware of the Object or prevented from running
    #[inline]
    pub unsafe fn promote_to_handle(self) -> Handle<T> {
        let untagged = self.data & !(ValueTag::Reference as u64);
        let ptr = untagged as *mut T;
        // SAFETY: valid pointer
        unsafe { Handle::from_ptr(ptr) }
    }
}

impl Tagged<i64> {
    pub fn as_i64(self) -> i64 {
        i64::from(self)
    }

    pub fn raw_i64(self) -> i64 {
        self.data.cast_signed()
    }
}

impl<T: Object> From<Tagged<T>> for Value {
    fn from(value: Tagged<T>) -> Self {
        value.as_value()
    }
}

impl<T: PtrSizedObject> From<T> for Tagged<T> {
    #[inline]
    fn from(value: T) -> Self {
        Self::new_value(value)
    }
}

impl<T: Object> Handle<T> {
    /// Cast a Handle<T> to a Handle<U>
    /// # Safety
    /// the layout of T and U must be at least partially the same at the same offsets
    /// for example if U or T is the prefix of the other.
    pub unsafe fn cast<U: Object>(self) -> Handle<U> {
        Handle {
            data: self.data,
            _marker: PhantomData,
        }
    }

    /// Create a handle from a pointer
    /// # Safety
    /// the pointer must be a valid heap object
    pub unsafe fn from_ptr(ptr: *mut T) -> Self {
        Self {
            data: ptr as _,
            _marker: PhantomData,
        }
    }
}

impl<T: Object> PartialEq for Handle<T> {
    fn eq(&self, other: &Self) -> bool {
        self.data == other.data
    }
}

impl<T: HeapObject> Handle<T> {
    #[inline]
    pub fn as_object(self) -> Tagged<T> {
        let raw = self.data;
        let tagged = raw | (ValueTag::Reference as u64);
        unsafe { Tagged::new_raw(tagged) }
    }

    #[inline]
    pub fn as_value(self) -> Value {
        self.as_object().as_value()
    }

    #[inline]
    pub fn as_value_handle(self) -> Handle<Value> {
        let raw = self.data;
        let tagged = raw | (ValueTag::Reference as u64);
        Handle::<Value> {
            data: tagged,
            _marker: PhantomData,
        }
    }

    #[inline]
    pub fn as_heap_value_handle(self) -> Handle<HeapValue> {
        let raw = self.data;
        let tagged = raw | (ValueTag::Reference as u64);
        Handle::<HeapValue> {
            data: tagged,
            _marker: PhantomData,
        }
    }

    #[inline]
    pub fn as_ptr(self) -> *mut T {
        self.data as _
    }

    /// Create a null handle
    /// # Safety
    /// only for initialization or super special cases
    /// must make sure to not dereference this
    pub unsafe fn null() -> Handle<T> {
        Self {
            data: 0,
            _marker: PhantomData,
        }
    }
}

impl<T: PtrSizedObject> Handle<T> {
    pub fn as_fixnum(self) -> Tagged<T> {
        let raw = self.data;
        let tagged = raw << 1;
        // SAFETY: we are typesafe and do the transformation
        unsafe { Tagged::new_raw(tagged) }
    }
}

impl Handle<Value> {
    /// convert handle of a value to a tagged value
    /// # Safety
    /// Value is already tagged,
    /// but Tagged<T> does not protect against GC invocations
    pub unsafe fn as_tagged<T: Object>(self) -> Tagged<T> {
        let tagged = self.data;
        // SAFETY: this is not safe, use at own caution
        unsafe { Tagged::new_raw(tagged) }
    }

    /// convert to a fixnum
    /// # Safety
    /// caller must make sure that the Value is representing a T: PtrSizedObject
    /// and not for example a pointer or header
    pub unsafe fn as_fixnum<T: PtrSizedObject + From<Tagged<T>>>(self) -> T {
        // SAFETY: this is not safe, use at own caution
        let tagged = unsafe { self.as_tagged() };
        T::from(tagged)
    }

    pub fn inner(self) -> Value {
        Value(self.data)
    }
}

impl<T: HeapObject> From<Handle<T>> for Handle<Value> {
    fn from(value: Handle<T>) -> Self {
        value.as_value_handle()
    }
}

impl From<i64> for Value {
    fn from(value: i64) -> Self {
        Value::from_fixnum(value)
    }
}

impl From<u64> for Value {
    fn from(value: u64) -> Self {
        Value::from_u64(value)
    }
}

impl From<usize> for Value {
    fn from(value: usize) -> Self {
        Value::from_usize(value)
    }
}

// this is safe, ptr sized are always valid hadnles
impl From<i64> for Handle<i64> {
    fn from(value: i64) -> Self {
        Handle {
            data: value.cast_unsigned(),
            _marker: PhantomData,
        }
    }
}

impl From<Handle<i64>> for Handle<Value> {
    fn from(value: Handle<i64>) -> Handle<Value> {
        let value = Value::from_u64(value.data);
        Handle {
            data: value.0,
            _marker: PhantomData,
        }
    }
}

impl From<Handle<Value>> for Value {
    fn from(value: Handle<Value>) -> Self {
        value.inner()
    }
}

// TODO-RUST: why does this not work?
// impl<T: PtrSizedObject> From<Tagged<T>> for T {
//     #[inline]
//     fn from(value: Tagged<T>) -> Self {
//         let raw= value.raw();
//         Self::from_ptr_sized(raw)
//     }
// }
impl<T: PtrSizedObject> From<Tagged<T>> for usize {
    #[inline]
    fn from(value: Tagged<T>) -> Self {
        let raw = value.raw();
        let untagged = raw >> 1;
        Self::from_ptr_sized(untagged)
    }
}
impl<T: PtrSizedObject> From<Tagged<T>> for u64 {
    #[inline]
    fn from(value: Tagged<T>) -> Self {
        let raw = value.raw();
        let untagged = raw >> 1;
        Self::from_ptr_sized(untagged)
    }
}
impl<T: PtrSizedObject> From<Tagged<T>> for i64 {
    #[inline]
    fn from(value: Tagged<T>) -> Self {
        let raw = value.raw();
        let untagged = raw >> 1;
        Self::from_ptr_sized(untagged)
    }
}

impl<T: HeapObject> Deref for Handle<T> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        // SAFETY: we know that Handle is always valid
        unsafe { &*self.as_ptr() }
    }
}

impl<T: HeapObject> DerefMut for Handle<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        // SAFETY: we know that Handle is always valid
        // of course, we must take thread safety into account here on the user side
        unsafe { &mut *self.as_ptr() }
    }
}

impl<T: PtrSizedObject> From<Tagged<T>> for Handle<Value> {
    fn from(value: Tagged<T>) -> Self {
        // Value is already tagged
        let data = value.data;
        Self {
            data,
            _marker: PhantomData,
        }
    }
}

impl Visitable for Value {}
impl Object for Value {
    fn lookup(&self, selector: Selector<'_>, link: Option<&VisitedLink>) -> LookupResult {
        if let Some(_num) = self.as_tagged_fixnum::<i64>() {
            let traits = selector.vm.specials.fixnum_traits;
            return traits.lookup(selector, link);
        }

        // Safety: if its not a fixnum it must be a heap object
        let object = unsafe { self.as_heap_handle_unchecked() };
        object.lookup(selector, link)
    }
}

impl Visitable for u64 {}
impl Object for u64 {}
impl PtrSizedObject for u64 {
    #[inline]
    fn to_ptr_sized(self) -> u64 {
        self
    }

    fn from_ptr_sized(value: u64) -> Self {
        value
    }
}

impl Visitable for usize {}
impl Object for usize {}
impl PtrSizedObject for usize {
    #[inline]
    fn to_ptr_sized(self) -> u64 {
        self as u64
    }
    fn from_ptr_sized(value: u64) -> Self {
        value as usize
    }
}

impl Visitable for i64 {}
impl Object for i64 {}
impl PtrSizedObject for i64 {
    #[inline]
    fn to_ptr_sized(self) -> u64 {
        self.cast_unsigned()
    }
    fn from_ptr_sized(value: u64) -> Self {
        value.cast_signed()
    }
}

impl<T> Visitable for *mut T {}
impl<T> Object for *mut T {}
impl<T> PtrSizedObject for *mut T {
    #[inline]
    fn to_ptr_sized(self) -> u64 {
        self as _
    }
    fn from_ptr_sized(value: u64) -> Self {
        value as _
    }
}

#[cfg(test)]
mod value_tests {
    use super::*;

    struct TestObj {
        n: i64,
        m: usize,
    }

    impl Visitable for TestObj {}
    impl Object for TestObj {}
    impl HeapObject for TestObj {}

    fn boxed_test_obj(n: i64, m: usize) -> Box<TestObj> {
        Box::new(TestObj { n, m })
    }

    #[test]
    fn value_from_fixnum_sets_low_bit_zero_and_reports_fixnum() {
        let v = Value::from_fixnum(42);
        assert_eq!(v.0 & 0b1, 0);

        assert!(
            v.is_fixnum(),
            "expected Value::is_fixnum to be true for fixnums"
        );
        assert!(
            !v.is_object(),
            "fixnum must not be reported as object/reference"
        );
        assert!(!v.is_header(), "fixnum must not be reported as header");
    }

    #[test]
    fn roundtrip_usize() {
        let val = 10usize;
        let tagged: Tagged<usize> = val.into();
        let orig: usize = tagged.into();
        assert!(val == orig)
    }

    #[test]
    fn tagged_i64_roundtrip_via_value() {
        let t: Tagged<i64> = Tagged::new_value(123);
        let v: Value = Value::from(t);
        assert!(v.is_fixnum());

        let t_back = v
            .as_tagged_fixnum::<i64>()
            .expect("should be tagged fixnum");
        assert_eq!(t_back.as_i64(), 123);
    }

    #[test]
    fn tagged_usize_roundtrip_via_value() {
        let t: Tagged<usize> = Tagged::new_value(0x1234usize);
        let v: Value = Value::from(t);
        assert!(v.is_fixnum());
        let t_back = v
            .as_tagged_fixnum::<usize>()
            .expect("should be tagged fixnum");

        let round: usize = t_back.into();
        assert_eq!(round, 0x1234usize);
    }

    #[test]
    fn tagged_restore_u64_matches_original_for_ptr_sized() {
        let original = 0xABCDu64;
        let t: Tagged<u64> = Tagged::new_value(original);
        assert_eq!(t.restore_u64(), original);
    }

    #[test]
    fn tagged_ptr_roundtrip_and_value_detection() {
        let mut obj = boxed_test_obj(7, 99);
        let raw: *mut TestObj = &mut *obj;

        let tagged_ptr: Tagged<TestObj> = Tagged::new_ptr(raw);
        assert_eq!(tagged_ptr.data & OBECT_TAG_MASK, ValueTag::Reference as u64);

        assert_eq!(tagged_ptr.as_ptr(), raw);

        let v: Value = Value::from(tagged_ptr);
        assert!(
            v.is_object(),
            "expected Value::is_object to be true for reference-tagged values"
        );
        assert!(
            !v.is_fixnum(),
            "object/tagged pointer must not be reported as fixnum"
        );

        let t2 = v
            .as_tagged_object::<TestObj>()
            .expect("should recover tagged object");
        assert_eq!(t2.as_ptr(), raw);
    }

    #[test]
    fn tagged_as_ref_and_as_mut_work_unsafely() {
        let mut obj = boxed_test_obj(1, 2);
        let tagged: Tagged<TestObj> = Tagged::new_ptr(&mut *obj);

        unsafe {
            let r: &TestObj = tagged.as_ref();
            assert_eq!(r.n, 1);
            assert_eq!(r.m, 2);

            let mref: &mut TestObj = tagged.as_mut();
            mref.n = 42;
            mref.m = 77;
        }

        assert_eq!(obj.n, 42);
        assert_eq!(obj.m, 77);
    }

    #[test]
    fn handle_from_fixnum_and_into_handle_value() {
        let h_i: Handle<i64> = Handle::from(321i64);
        let h_v: Handle<Value> = h_i.into();
        let v = h_v.inner();
        assert!(v.is_fixnum());

        let t_fix = v
            .as_tagged_fixnum::<i64>()
            .expect("should be tagged fixnum");
        assert_eq!(t_fix.as_i64(), 321);
    }

    #[test]
    fn handle_object_as_object_and_deref() {
        let mut boxed = boxed_test_obj(10, 20);
        let ptr = &mut *boxed as *mut TestObj;

        let handle: Handle<TestObj> = unsafe { Handle::from_ptr(ptr) };
        let tagged = handle.as_object();
        assert_eq!(tagged.data & OBECT_TAG_MASK, ValueTag::Reference as u64);

        assert_eq!(handle.n, 10);
        assert_eq!(handle.m, 20);

        {
            let mut h2 = handle;
            let r: &mut TestObj = &mut *h2;
            r.n = 123;
            r.m = 456;
        }
        assert_eq!(unsafe { (*ptr).n }, 123);
        assert_eq!(unsafe { (*ptr).m }, 456);
    }

    #[test]
    fn handle_cast_between_object_and_value() {
        let mut boxed = boxed_test_obj(5, 6);
        let ptr = &mut *boxed as *mut TestObj;

        let h_obj: Handle<TestObj> = unsafe { Handle::from_ptr(ptr) };
        let h_val: Handle<Value> = unsafe { h_obj.cast::<Value>() };
        let h_obj_back: Handle<TestObj> = unsafe { h_val.cast::<TestObj>() };

        assert_eq!(h_obj.as_ptr(), h_obj_back.as_ptr());
    }

    #[test]
    fn object_and_fixnum_are_mutually_exclusive() {
        let v_fix = Value::from_fixnum(-7);
        assert!(v_fix.is_fixnum());
        assert!(!v_fix.is_object(), "fixnum must not be object");

        let mut boxed = boxed_test_obj(0, 0);
        let tagged_ptr = Tagged::<TestObj>::new_ptr(&mut *boxed);
        let v_obj: Value = Value::from(tagged_ptr);
        assert!(v_obj.is_object());
        assert!(!v_obj.is_fixnum(), "object must not be fixnum");
    }

    #[test]
    fn header_tag_detection_when_low_two_bits_are_header() {
        let raw = 0u64 | (ValueTag::Header as u64);
        let v = Value(raw);
        assert_eq!(raw & OBECT_TAG_MASK, ValueTag::Header as u64);
        assert!(
            v.is_header(),
            "Value::is_header should be true when low two bits indicate header"
        );
        assert!(!v.is_fixnum());
        assert!(!v.is_object());
    }
}
