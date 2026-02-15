use crate::Value;

/// Property flags for a slot within a [`Map`](crate::Map).
///
/// Stored in the low 16 bits of the slot's `meta` field.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(transparent)]
pub struct SlotFlags(pub u16);

impl SlotFlags {
    pub const NONE: Self = Self(0);

    /// Read-access slot for an assignable property.
    /// `value` stores the byte offset of the data within the owning object.
    pub const ASSIGNABLE: Self = Self(1 << 0);

    /// Write-access slot for an assignable property.
    /// Paired with [`ASSIGNABLE`](Self::ASSIGNABLE); same byte offset.
    pub const ASSIGNMENT: Self = Self(1 << 1);

    /// Constant slot. `value` stores the actual value directly in the map.
    pub const CONSTANT: Self = Self(1 << 2);

    /// Slot is visible to enumeration.
    pub const ENUMERABLE: Self = Self(1 << 3);

    /// Slot is a parent link — the lookup algorithm traverses it.
    pub const PARENT: Self = Self(1 << 4);

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

/// A slot descriptor embedded inline in a [`Map`](crate::Map).
///
/// - `meta`:  low 16 bits are [`SlotFlags`]; upper 48 bits reserved.
/// - `name`:  tagged value identifying the slot (typically a symbol reference).
/// - `value`: depends on slot kind:
///   - **Constant**: the actual tagged value.
///   - **Assignable / Assignment**: byte offset (as fixnum) into the object body.
#[derive(Clone, Copy)]
#[repr(C)]
pub struct Slot {
    pub meta: u64,
    pub name: Value,
    pub value: Value,
}

const _: () = assert!(size_of::<Slot>() == 24);

impl Slot {
    #[inline(always)]
    pub fn new(flags: SlotFlags, name: Value, value: Value) -> Self {
        Self {
            meta: flags.0 as u64,
            name,
            value,
        }
    }

    #[inline(always)]
    pub fn flags(&self) -> SlotFlags {
        SlotFlags(self.meta as u16)
    }

    #[inline(always)]
    pub fn is_parent(&self) -> bool {
        self.flags().contains(SlotFlags::PARENT)
    }

    #[inline(always)]
    pub fn is_assignable(&self) -> bool {
        self.flags().contains(SlotFlags::ASSIGNABLE)
    }

    #[inline(always)]
    pub fn is_assignment(&self) -> bool {
        self.flags().contains(SlotFlags::ASSIGNMENT)
    }

    #[inline(always)]
    pub fn is_constant(&self) -> bool {
        self.flags().contains(SlotFlags::CONSTANT)
    }
}

impl core::fmt::Debug for Slot {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Slot")
            .field("flags", &self.flags())
            .field("name", &self.name)
            .field("value", &self.value)
            .finish()
    }
}
