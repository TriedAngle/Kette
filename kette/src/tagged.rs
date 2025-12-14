//! Value: any raw value, small integer/reference/header
//!
//! Tagged<T>: same as Value but but typed (= type safe) for easier rust side type declaration, but not
//! safe to use
//!
//! Handle<T>: untagged value, small integer or reference, is safe to use, GC does not clear/move this
//! also implements Deref and DerefMut
use std::{
    fmt::Debug,
    hash,
    marker::PhantomData,
    ops::{Deref, DerefMut},
};

use crate::{HeapObject, HeapValue, Object, PtrSizedObject, Visitable};

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
#[repr(C)]
#[derive(PartialEq, Eq)]
pub struct Tagged<T: Object> {
    data: u64,
    _marker: PhantomData<*mut T>,
}

/// GC safe Reference to a HeapObject or an SMI
///
/// Wraps a **Tagged** value (not a raw pointer).
/// It guarantees that the underlying object is kept alive by the GC.
///
/// Memory Layout: Identical to `Value` and `Tagged<T>`.
#[repr(C)]
pub struct Handle<T: Object> {
    data: u64,
    _marker: PhantomData<*mut T>,
}

// SAFETY: safe as long as not abused in VM, needs extra locking there potentially
unsafe impl Send for Value {}
// SAFETY: safe as long as not abused in VM, needs extra locking there potentially
unsafe impl Sync for Value {}

// SAFETY: safe as long as not abused in VM, needs extra locking there potentially
unsafe impl<T: Object> Send for Tagged<T> {}
// SAFETY: safe as long as not abused in VM, needs extra locking there potentially
unsafe impl<T: Object> Sync for Tagged<T> {}

// SAFETY: safe as long as not abused in VM, needs extra locking there potentially
unsafe impl<T: Object> Send for Handle<T> {}
// SAFETY: safe as long as not abused in VM, needs extra locking there potentially
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
    /// Caller must make sure Value doesn't get allocated/moved without GC knowing
    pub unsafe fn as_handle_unchecked(self) -> Handle<Value> {
        Handle {
            data: self.0,
            _marker: PhantomData,
        }
    }

    /// Create a handle from a value
    /// # Safety
    /// Caller must make sure Value doesn't get allocated/moved without GC knowing
    pub unsafe fn as_heap_handle_unchecked(self) -> Handle<HeapValue> {
        Handle {
            data: self.0,
            _marker: PhantomData,
        }
    }
}

impl<T: Object> Tagged<T> {
    #[inline]
    /// Create a new Tagged from the value
    /// # Safety
    /// the raw value must be correctly tagged and either a fixnum or a reference to a heap object
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

    pub fn as_tagged_value(self) -> Tagged<Value> {
        Tagged {
            data: self.data,
            _marker: PhantomData,
        }
    }

    /// cast Tagged<T> to Tagged<U>
    /// # Safety
    /// T and U must have same layout, or T represents U (in case of Value)
    pub unsafe fn cast<U: Object>(self) -> Tagged<U> {
        Tagged {
            data: self.data,
            _marker: PhantomData,
        }
    }
}

impl<T: PtrSizedObject> Tagged<T> {
    #[inline]
    pub fn new_value(value: T) -> Self {
        let value = value.to_ptr_sized();
        let tagged = value << 1;
        // SAFETY: this is safe, this is guaranted to be correctly tagged
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
        // SAFETY: this is safe, we check before
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
        Handle {
            data: self.data,
            _marker: PhantomData,
        }
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
        let value = ptr as u64;
        debug_assert_eq!(
            value & OBECT_TAG_MASK,
            0,
            "pointer must be aligned so low 2 bits are free"
        );
        let tagged = value | (ValueTag::Reference as u64);
        Self {
            data: tagged,
            _marker: PhantomData,
        }
    }

    /// Convert to a Tagged<T>.
    ///
    /// This is safe as long as T and U are "the same".
    /// Handle is also stricter than Tagged
    #[inline]
    pub fn as_tagged<U: Object>(self) -> Tagged<U> {
        // SAFETY: this is safe as long as the contract described holds
        unsafe { Tagged::new_raw(self.data) }
    }

    /// Returns the internal tagged raw bits
    #[inline]
    pub fn raw_tagged_u64(self) -> u64 {
        self.data
    }

    pub fn as_value(self) -> Value {
        Value(self.data)
    }
}

impl<T: Object> PartialEq for Handle<T> {
    fn eq(&self, other: &Self) -> bool {
        self.data == other.data
    }
}

impl<T: Object> Eq for Handle<T> {}

impl<T: Object> hash::Hash for Handle<T> {
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        state.write_u64(self.data);
    }
}

impl<T: HeapObject> Handle<T> {
    #[inline]
    pub fn as_object(self) -> Tagged<T> {
        // SAFETY: this is safe, Handle is stricter than Tagged
        unsafe { Tagged::new_raw(self.data) }
    }

    #[inline]
    pub fn as_value_handle(self) -> Handle<Value> {
        Handle::<Value> {
            data: self.data,
            _marker: PhantomData,
        }
    }

    #[inline]
    pub fn as_heap_value_handle(self) -> Handle<HeapValue> {
        Handle::<HeapValue> {
            data: self.data,
            _marker: PhantomData,
        }
    }

    #[inline]
    pub fn as_ptr(self) -> *mut T {
        debug_assert_eq!(
            self.data & OBECT_TAG_MASK,
            ValueTag::Reference as u64,
            "Handle data must be tagged as a Reference to be converted to a pointer"
        );
        let untagged = self.data & !(ValueTag::Reference as u64);
        untagged as _
    }

    /// Create a null handle
    /// # Safety
    /// only for initialization or super special cases
    /// must make sure to not dereference this
    pub unsafe fn null() -> Handle<T> {
        // We tag it as a reference, so it looks like a valid (but null) tagged pointer
        let null_tagged = ValueTag::Reference as u64;
        Self {
            data: null_tagged,
            _marker: PhantomData,
        }
    }
}

impl<T: PtrSizedObject> Handle<T> {
    pub fn as_fixnum(self) -> Tagged<T> {
        // SAFETY: Handle is already tagged.
        unsafe { Tagged::new_raw(self.data) }
    }
}

impl Handle<Value> {
    /// convert handle of a value to a tagged value
    /// # Safety
    /// Value is already tagged,
    /// but Tagged<T> does not protect against GC invocations
    pub unsafe fn into_tagged<T: Object>(self) -> Tagged<T> {
        // SAFETY: safe if adhering to the safety contract of this function
        unsafe { Tagged::new_raw(self.data) }
    }

    /// convert to a fixnum
    /// # Safety
    /// caller must make sure that the Value is representing a T: PtrSizedObject
    /// and not for example a pointer or header
    pub unsafe fn as_fixnum<T: PtrSizedObject + From<Tagged<T>>>(self) -> T {
        // SAFETY: safe if adhering to the safety contract of this function
        let tagged = unsafe { Tagged::new_raw(self.data) };
        T::from(tagged)
    }

    pub fn inner(self) -> Value {
        Value(self.data)
    }

    pub fn is_fixnum(&self) -> bool {
        self.data & 0b1 == ValueTag::Fixnum as u64
    }

    pub fn is_object(&self) -> bool {
        self.data & OBECT_TAG_MASK == ValueTag::Reference as u64
    }

    /// Get a generic HeapValue from a Value
    /// # Safety
    /// user must make sure this is a heap value
    #[inline]
    pub unsafe fn as_heap_value_handle(self) -> Handle<HeapValue> {
        Handle::<HeapValue> {
            data: self.data,
            _marker: PhantomData,
        }
    }
}

impl<T: Object> From<Handle<T>> for Tagged<T> {
    fn from(value: Handle<T>) -> Self {
        Self {
            data: value.data,
            _marker: PhantomData,
        }
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

// this is safe, ptr sized are always valid handles
impl From<i64> for Handle<i64> {
    fn from(value: i64) -> Self {
        let casted = value.cast_unsigned();
        let tagged = casted << 1;
        Handle {
            data: tagged,
            _marker: PhantomData,
        }
    }
}

impl From<Handle<i64>> for Handle<Value> {
    fn from(value: Handle<i64>) -> Handle<Value> {
        Handle {
            data: value.data,
            _marker: PhantomData,
        }
    }
}

impl From<Handle<Value>> for Value {
    fn from(value: Handle<Value>) -> Self {
        value.inner()
    }
}

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
        // SAFETY: we know that Handle is always valid and kept alive by GC.
        // We must strip the tag to get the raw pointer.
        unsafe { &*self.as_ptr() }
    }
}

impl<T: HeapObject> DerefMut for Handle<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        // SAFETY: Handle is valid.
        // Thread safety is the user's responsibility.
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

impl<T: Object> Debug for Handle<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Handle")
            .field("type", &std::any::type_name::<T>())
            .field("value", &format!("{:#x}", self.data))
            .finish()
    }
}

impl<T: Object> Debug for Tagged<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Tagged")
            .field("type", &std::any::type_name::<T>())
            .field("value", &format!("{:#x}", self.data))
            .finish()
    }
}

pub mod transmute {
    use crate::{Handle, Object, Tagged, Value};

    const _: [(); std::mem::size_of::<Handle<Value>>()] =
        [(); std::mem::size_of::<Value>()];
    const _: [(); std::mem::align_of::<Handle<Value>>()] =
        [(); std::mem::align_of::<Value>()];
    const _: [(); std::mem::size_of::<Tagged<Value>>()] =
        [(); std::mem::size_of::<Value>()];
    const _: [(); std::mem::align_of::<Tagged<Value>>()] =
        [(); std::mem::align_of::<Value>()];

    /// Reinterpret a slice of `Handle<Value>` as a slice of `Value`.
    ///
    /// Safe because the memory layout is identical and a handle always contains
    /// a well-formed tagged value.
    #[inline]
    pub fn handles_as_values<T: Object>(handles: &[Handle<T>]) -> &[Value] {
        let ptr = handles.as_ptr() as *const Value;
        // SAFETY: identical layout (see const assertions) and same length.
        unsafe { std::slice::from_raw_parts(ptr, handles.len()) }
    }

    /// Reinterpret a mutable slice of `Handle<Value>` as a mutable slice of `Value`.
    #[inline]
    pub fn handles_as_values_mut<T: Object>(
        handles: &mut [Handle<T>],
    ) -> &mut [Value] {
        let ptr = handles.as_mut_ptr() as *mut Value;
        // SAFETY: identical layout (see const assertions) and same length.
        unsafe { std::slice::from_raw_parts_mut(ptr, handles.len()) }
    }

    /// Reinterpret a slice of `Value` as a slice of `Handle<Value>`.
    ///
    /// # Safety
    /// The caller must ensure that each `Value` in the slice is safe to be treated
    /// as a handle
    ///
    /// This is equivalent to calling `Value::as_handle_unchecked` on each element.
    #[inline]
    pub unsafe fn values_as_handles(values: &[Value]) -> &[Handle<Value>] {
        let ptr = values.as_ptr() as *const Handle<Value>;
        // SAFETY: caller upholds the contract above.
        unsafe { std::slice::from_raw_parts(ptr, values.len()) }
    }

    /// Reinterpret a mutable slice of `Value` as a mutable slice of `Handle<Value>`.
    ///
    /// # Safety
    /// Same contract as [`values_as_handles`].
    #[inline]
    pub unsafe fn values_as_handles_mut(
        values: &mut [Value],
    ) -> &mut [Handle<Value>] {
        let ptr = values.as_mut_ptr() as *mut Handle<Value>;
        // SAFETY: caller upholds the contract above.
        unsafe { std::slice::from_raw_parts_mut(ptr, values.len()) }
    }

    /// Reinterpret a slice of `Tagged<T>` as a slice of `Value`.
    ///
    /// Always safe: `Tagged<Value>` is just a typed view of raw tagged bits.
    #[inline]
    pub fn tagged_values_as_values<T: Object>(
        tagged: &[Tagged<T>],
    ) -> &[Value] {
        let ptr = tagged.as_ptr() as *const Value;
        // SAFETY: identical layout (see const assertions) and same length.
        unsafe { std::slice::from_raw_parts(ptr, tagged.len()) }
    }

    /// Reinterpret a mutable slice of `Tagged<T>` as a mutable slice of `Value`.
    #[inline]
    pub fn tagged_values_as_values_mut<T: Object>(
        tagged: &mut [Tagged<T>],
    ) -> &mut [Value] {
        let ptr = tagged.as_mut_ptr() as *mut Value;
        // SAFETY: identical layout (see const assertions) and same length.
        unsafe { std::slice::from_raw_parts_mut(ptr, tagged.len()) }
    }

    /// Reinterpret a slice of `Value` as a slice of `Tagged<Value>`.
    ///
    /// Safe because `Tagged<Value>` does not add invariants over `Value`.
    #[inline]
    pub fn values_as_tagged_values(values: &[Value]) -> &[Tagged<Value>] {
        let ptr = values.as_ptr() as *const Tagged<Value>;
        // SAFETY: identical layout (see const assertions) and same length.
        unsafe { std::slice::from_raw_parts(ptr, values.len()) }
    }

    /// Reinterpret a mutable slice of `Value` as a mutable slice of `Tagged<Value>`.
    #[inline]
    pub fn values_as_tagged_values_mut(
        values: &mut [Value],
    ) -> &mut [Tagged<Value>] {
        let ptr = values.as_mut_ptr() as *mut Tagged<Value>;
        // SAFETY: identical layout (see const assertions) and same length.
        unsafe { std::slice::from_raw_parts_mut(ptr, values.len()) }
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
        assert_eq!(
            tagged_ptr.data & OBECT_TAG_MASK,
            ValueTag::Reference as u64
        );

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
    fn handle_stores_tagged_data_internally() {
        let mut boxed = boxed_test_obj(10, 20);
        let ptr = &mut *boxed as *mut TestObj;

        let handle: Handle<TestObj> = unsafe { Handle::from_ptr(ptr) };

        // The internal data should have the reference tag bit (0b01) set
        assert_eq!(handle.data & OBECT_TAG_MASK, ValueTag::Reference as u64);

        // Masking it should equal the original pointer
        assert_eq!(handle.data & !OBECT_TAG_MASK, ptr as u64);
    }

    #[test]
    fn handle_object_deref_masks_tag_correctly() {
        let mut boxed = boxed_test_obj(10, 20);
        let ptr = &mut *boxed as *mut TestObj;

        let handle: Handle<TestObj> = unsafe { Handle::from_ptr(ptr) };

        // Dereferencing involves masking the tag, then reading memory
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
    fn handle_value_retains_fixnum_tag() {
        // Create an i64 handle
        let h_i: Handle<i64> = Handle::from(321i64);
        // Cast to Value handle
        let h_v: Handle<Value> = h_i.into();

        // The handle data should look like a fixnum (tag 0)
        assert!(h_v.is_fixnum());
        assert!(!h_v.is_object());

        // Recover value
        let v = h_v.inner();
        assert_eq!(v.as_tagged_fixnum::<i64>().unwrap().as_i64(), 321);
    }

    #[test]
    fn handle_cast_between_object_and_value() {
        let mut boxed = boxed_test_obj(5, 6);
        let ptr = &mut *boxed as *mut TestObj;

        let h_obj: Handle<TestObj> = unsafe { Handle::from_ptr(ptr) };
        let h_val: Handle<Value> = unsafe { h_obj.cast::<Value>() };

        assert!(h_val.is_object());

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

    use super::transmute;

    #[test]
    fn slice_handle_value_view_roundtrip() {
        let h1: Handle<i64> = Handle::from(1i64);
        let h2: Handle<i64> = Handle::from(2i64);

        let handles: [Handle<Value>; 2] = [h1.into(), h2.into()];

        let values = transmute::handles_as_values(&handles);
        assert!(values[0].is_fixnum());
        assert_eq!(values[0].as_tagged_fixnum::<i64>().unwrap().as_i64(), 1);
        assert_eq!(values[1].as_tagged_fixnum::<i64>().unwrap().as_i64(), 2);

        let handles_back = unsafe { transmute::values_as_handles(values) };
        let v0 = handles_back[0].inner();
        let v1 = handles_back[1].inner();

        assert_eq!(v0.as_tagged_fixnum::<i64>().unwrap().as_i64(), 1);
        assert_eq!(v1.as_tagged_fixnum::<i64>().unwrap().as_i64(), 2);
    }

    #[test]
    fn slice_tagged_value_view_roundtrip() {
        let t1: Tagged<i64> = Tagged::new_value(10);
        let t2: Tagged<i64> = Tagged::new_value(11);

        let tagged: [Tagged<Value>; 2] =
            [t1.as_tagged_value(), t2.as_tagged_value()];

        let values = transmute::tagged_values_as_values(&tagged);
        assert!(values[0].is_fixnum());
        assert!(values[1].is_fixnum());

        let tagged_back = transmute::values_as_tagged_values(values);
        assert_eq!(
            tagged_back[0]
                .as_value()
                .as_tagged_fixnum::<i64>()
                .unwrap()
                .as_i64(),
            10
        );
        assert_eq!(
            tagged_back[1]
                .as_value()
                .as_tagged_fixnum::<i64>()
                .unwrap()
                .as_i64(),
            11
        );
    }
}
