use crate::Value;

/// Well-known singleton objects and trait maps.
///
/// Holds tagged [`Value`] references to objects that the VM needs for
/// core operations and for looking up methods on primitive types that
/// don't carry their own map pointer.
///
/// **Objects are not allocated here.** They must be allocated on the heap
/// first and then stored as tagged references. Pass this struct by
/// reference (`&SpecialObjects`) to subsystems that need it.
pub struct SpecialObjects {
    // ── Singletons ─────────────────────────────────────────────────
    /// The canonical `None` object.
    pub none: Value,

    /// The canonical `true` object.
    pub true_obj: Value,

    /// The canonical `false` object.
    pub false_obj: Value,

    /// The map that describes all other maps (self-referential).
    pub map_map: Value,

    /// The root Object prototype.
    pub object: Value,

    /// Methods / slots for [`Block`](crate::Block) objects.
    pub block_traits: Value,

    // ── Trait maps for map-less primitives ──────────────────────────
    /// Methods / slots for [`Array`](crate::Array) objects.
    pub array_traits: Value,

    /// Methods / slots for [`ByteArray`](crate::ByteArray) objects.
    pub bytearray_traits: Value,

    /// Methods / slots for [`BigNum`](crate::BigNum) objects.
    pub bignum_traits: Value,

    /// Methods / slots for [`Alien`](crate::Alien) objects.
    pub alien_traits: Value,

    /// Methods / slots for [`VMString`](crate::VMString) objects.
    pub string_traits: Value,

    /// Methods / slots for [`VMSymbol`](crate::VMSymbol) objects.
    pub symbol_traits: Value,

    /// Methods / slots for [`Ratio`](crate::Ratio) objects.
    pub ratio_traits: Value,

    /// Methods / slots for fixnum (tagged integer) values.
    pub fixnum_traits: Value,

    /// Methods / slots for [`Code`](crate::Code) objects.
    pub code_traits: Value,

    /// Methods / slots for [`Float`](crate::Float) objects.
    pub float_traits: Value,

    /// Root Mirror prototype object.
    pub mirror: Value,
}
