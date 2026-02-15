/// Tag constants.
const FIXNUM_MASK: u64 = 0b1;
const TAG_MASK: u64 = 0b11;
const REF_TAG: u64 = 0b01;
const HEADER_TAG: u64 = 0b11;

/// A tagged 64-bit value.
///
/// Encoding:
/// - **Fixnum**:    `...XXXXX0` — 63-bit signed integer (low bit 0).
/// - **Reference**: `...XXXX01` — heap pointer (mask low 2 bits; requires 4-byte alignment).
/// - **Header**:    `...XXXX11` — only valid as the first word of a heap object.
#[derive(Clone, Copy, PartialEq, Eq)]
#[repr(transparent)]
pub struct Value(u64);

impl Value {
    #[inline(always)]
    pub const fn raw(self) -> u64 {
        self.0
    }

    #[inline(always)]
    pub const fn from_raw(raw: u64) -> Self {
        Self(raw)
    }

    // ── Fixnum ─────────────────────────────────────────────────────

    #[inline(always)]
    pub const fn is_fixnum(self) -> bool {
        self.0 & FIXNUM_MASK == 0
    }

    #[inline(always)]
    pub fn from_i64(n: i64) -> Self {
        debug_assert!(
            (-(1i64 << 62)..(1i64 << 62)).contains(&n),
            "fixnum overflow: {n}"
        );
        Self((n << 1) as u64)
    }

    /// # Safety
    ///
    /// The value must be a fixnum.
    #[inline(always)]
    pub unsafe fn to_i64(self) -> i64 {
        debug_assert!(self.is_fixnum());
        (self.0 as i64) >> 1
    }

    // ── Reference ──────────────────────────────────────────────────

    #[inline(always)]
    pub const fn is_ref(self) -> bool {
        self.0 & TAG_MASK == REF_TAG
    }

    #[inline(always)]
    pub fn from_ptr<T>(ptr: *const T) -> Self {
        let addr = ptr as u64;
        debug_assert!(addr & TAG_MASK == 0, "pointer not aligned");
        Self(addr | REF_TAG)
    }

    #[inline(always)]
    pub const fn ref_bits(self) -> u64 {
        self.0 & !TAG_MASK
    }

    /// # Safety
    ///
    /// The value must be a reference to a valid, live `T`.
    #[inline(always)]
    pub unsafe fn as_ref<T>(&self) -> &T {
        debug_assert!(self.is_ref());
        &*(self.ref_bits() as *const T)
    }

    /// # Safety
    ///
    /// The value must be a reference to a valid, live `T`, and no other
    /// references to it may exist.
    #[inline(always)]
    pub unsafe fn as_mut<T>(&mut self) -> &mut T {
        debug_assert!(self.is_ref());
        &mut *(self.ref_bits() as *mut T)
    }

    #[inline(always)]
    pub const fn is_header(self) -> bool {
        self.0 & TAG_MASK == HEADER_TAG
    }
}

impl core::fmt::Debug for Value {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        if self.is_fixnum() {
            write!(f, "Fixnum({})", unsafe { self.to_i64() })
        } else if self.is_ref() {
            write!(f, "Ref(0x{:x})", self.ref_bits())
        } else {
            write!(f, "Header(0x{:016x})", self.0)
        }
    }
}
