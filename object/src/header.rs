use std::sync::atomic::{AtomicU8, Ordering};

/// Object type tag stored in bits 2..7 of the header's first byte.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum ObjectType {
    Slots = 0,
    Map,
    Array,
    ByteArray,
    Code,
    Block,
    BigNum,
    Alien,
    Str,
    Ratio,
    Float,
}

impl ObjectType {
    pub const COUNT: usize = Self::Float as usize + 1;
}

/// GC / bookkeeping flags stored atomically in the header.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(transparent)]
pub struct HeaderFlags(pub u8);

impl HeaderFlags {
    pub const NONE: Self = Self(0);
    pub const REMEMBERED: Self = Self(1 << 0);
    pub const PINNED: Self = Self(1 << 1);
    pub const ESCAPING: Self = Self(1 << 2);
    pub const ESCAPED: Self = Self(1 << 3);

    #[inline(always)]
    pub const fn contains(self, flag: Self) -> bool {
        self.0 & flag.0 == flag.0
    }

    #[inline(always)]
    pub const fn with(self, flag: Self) -> Self {
        Self(self.0 | flag.0)
    }

    #[inline(always)]
    pub const fn without(self, flag: Self) -> Self {
        Self(self.0 & !flag.0)
    }
}

const HEADER_TAG: u8 = 0b11;

/// The 8-byte header at the start of every heap object.
///
/// ```text
/// byte 0:    [tag:2 = 0b11] [object_type:6]
/// byte 1:    flags (atomic) — Remembered | Pinned | Escaping | Escaped
/// byte 2:    age   (atomic) — GC generation counter
/// bytes 3‥7: reserved (zero)
/// ```
///
/// On little-endian systems, reading these 8 bytes as a `u64` yields a
/// value whose low 2 bits are `0b11`, which [`Value::is_header`] detects.
#[repr(C)]
pub struct Header {
    tag_and_type: u8,
    flags: AtomicU8,
    age: AtomicU8,
    _reserved: [u8; 5],
}

const _: () = assert!(size_of::<Header>() == 8);

impl Header {
    pub fn new(object_type: ObjectType) -> Self {
        Self {
            tag_and_type: ((object_type as u8) << 2) | HEADER_TAG,
            flags: AtomicU8::new(0),
            age: AtomicU8::new(0),
            _reserved: [0; 5],
        }
    }

    #[inline(always)]
    pub fn object_type(&self) -> ObjectType {
        let raw = self.tag_and_type >> 2;
        debug_assert!((raw as usize) < ObjectType::COUNT);
        unsafe { core::mem::transmute::<u8, ObjectType>(raw) }
    }

    // ── flags ──────────────────────────────────────────────────────

    #[inline(always)]
    pub fn flags(&self) -> HeaderFlags {
        HeaderFlags(self.flags.load(Ordering::Relaxed))
    }

    #[inline(always)]
    pub fn set_flags(&self, flags: HeaderFlags) {
        self.flags.store(flags.0, Ordering::Relaxed);
    }

    #[inline(always)]
    pub fn has_flag(&self, flag: HeaderFlags) -> bool {
        self.flags().contains(flag)
    }

    #[inline(always)]
    pub fn add_flag(&self, flag: HeaderFlags) {
        self.flags.fetch_or(flag.0, Ordering::Relaxed);
    }

    #[inline(always)]
    pub fn remove_flag(&self, flag: HeaderFlags) {
        self.flags.fetch_and(!flag.0, Ordering::Relaxed);
    }

    // ── age ────────────────────────────────────────────────────────

    #[inline(always)]
    pub fn age(&self) -> u8 {
        self.age.load(Ordering::Relaxed)
    }

    #[inline(always)]
    pub fn set_age(&self, age: u8) {
        self.age.store(age, Ordering::Relaxed);
    }

    #[inline(always)]
    pub fn increment_age(&self) -> u8 {
        self.age.fetch_add(1, Ordering::Relaxed)
    }

    /// Atomically compare-exchange the age field.
    /// Returns `Ok(current)` on success, `Err(actual)` on failure.
    #[inline(always)]
    pub fn compare_exchange_age(&self, current: u8, new: u8) -> Result<u8, u8> {
        self.age.compare_exchange(current, new, Ordering::Relaxed, Ordering::Relaxed)
    }

    /// Atomically OR flags and return the *previous* flags value.
    #[inline(always)]
    pub fn fetch_or_flags(&self, flag: HeaderFlags) -> HeaderFlags {
        HeaderFlags(self.flags.fetch_or(flag.0, Ordering::Relaxed))
    }
}

impl core::fmt::Debug for Header {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Header")
            .field("type", &self.object_type())
            .field("flags", &self.flags())
            .field("age", &self.age())
            .finish()
    }
}
