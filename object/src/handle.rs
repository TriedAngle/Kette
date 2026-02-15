use crate::Value;
use core::marker::PhantomData;

/// A typed tagged value.
///
/// The underlying bits are the same as [`Value`] but `T` indicates the
/// expected heap type for reference values. Dereferencing is unsafe — the
/// caller must guarantee the value actually points to a valid `T`.
#[derive(Clone, Copy, PartialEq, Eq)]
#[repr(transparent)]
pub struct Tagged<T> {
    value: Value,
    _marker: PhantomData<*const T>,
}

impl<T> Tagged<T> {
    #[inline(always)]
    pub fn from_value(value: Value) -> Self {
        Self { value, _marker: PhantomData }
    }

    #[inline(always)]
    pub fn value(self) -> Value {
        self.value
    }

    #[inline(always)]
    pub fn is_fixnum(self) -> bool {
        self.value.is_fixnum()
    }

    #[inline(always)]
    pub fn is_ref(self) -> bool {
        self.value.is_ref()
    }

    // ── Fixnum helpers ─────────────────────────────────────────────

    /// Extract the fixnum value as `i64`.
    ///
    /// # Safety
    ///
    /// The value must be a fixnum.
    #[inline(always)]
    pub unsafe fn as_i64(self) -> i64 {
        self.value.to_i64()
    }

    /// Extract the fixnum value as `u64`.
    ///
    /// # Safety
    ///
    /// The value must be a non-negative fixnum.
    #[inline(always)]
    pub unsafe fn as_u64(self) -> u64 {
        let n = self.value.to_i64();
        debug_assert!(n >= 0, "as_u64 on negative fixnum: {n}");
        n as u64
    }

    /// Extract the fixnum value as `usize`.
    ///
    /// # Safety
    ///
    /// The value must be a non-negative fixnum.
    #[inline(always)]
    pub unsafe fn as_usize(self) -> usize {
        let n = self.value.to_i64();
        debug_assert!(n >= 0, "as_usize on negative fixnum: {n}");
        n as usize
    }

    // ── Reference helpers ──────────────────────────────────────────

    /// Dereference as a shared reference to `T`.
    ///
    /// # Safety
    ///
    /// The value must be a reference to a valid, live `T`.
    #[inline(always)]
    pub unsafe fn as_ref(&self) -> &T {
        self.value.as_ref()
    }

    /// Dereference as a mutable reference to `T`.
    ///
    /// # Safety
    ///
    /// The value must be a reference to a valid, live `T`, and no other
    /// references to it may exist.
    #[inline(always)]
    pub unsafe fn as_mut(&mut self) -> &mut T {
        self.value.as_mut()
    }
}

impl<T> core::fmt::Debug for Tagged<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "Tagged({:?})", self.value)
    }
}

impl<T> From<Value> for Tagged<T> {
    fn from(value: Value) -> Self {
        Self::from_value(value)
    }
}

impl<T> From<Tagged<T>> for Value {
    fn from(handle: Tagged<T>) -> Self {
        handle.value
    }
}
