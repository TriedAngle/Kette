use object::{Alien, Array, BigNum, Float, Header, ObjectType, Ratio, Value};

use crate::interpreter::{InterpreterState, RuntimeError};
use crate::VM;

pub mod alien;
pub mod array;
pub mod r#become;
pub mod bignum;
pub mod block;
pub mod bytearray;
pub mod extend;
pub mod fixnum;
pub mod float;
pub mod mirror;
pub mod object_clone;
pub mod pin;
pub mod ratio;
pub mod string;
pub mod vm;

pub type PrimitiveFn = fn(
    &mut VM,
    &mut InterpreterState,
    Value,
    &[Value],
) -> Result<Value, RuntimeError>;

#[derive(Clone, Copy)]
pub struct PrimitiveDesc {
    pub name: &'static str,
    pub arity: u8,
    pub func: PrimitiveFn,
}

impl PrimitiveDesc {
    pub const fn new(name: &'static str, arity: u8, func: PrimitiveFn) -> Self {
        Self { name, arity, func }
    }
}

pub fn default_primitives() -> Vec<PrimitiveDesc> {
    vec![
        PrimitiveDesc::new("fixnum_add", 1, fixnum::fixnum_add),
        PrimitiveDesc::new("fixnum_sub", 1, fixnum::fixnum_sub),
        PrimitiveDesc::new("fixnum_mul", 1, fixnum::fixnum_mul),
        PrimitiveDesc::new("fixnum_div", 1, fixnum::fixnum_div),
        PrimitiveDesc::new("fixnum_mod", 1, fixnum::fixnum_mod),
        PrimitiveDesc::new("fixnum_neg", 0, fixnum::fixnum_neg),
        PrimitiveDesc::new("fixnum_to_bignum", 0, fixnum::fixnum_to_bignum),
        PrimitiveDesc::new("fixnum_to_ratio", 0, fixnum::fixnum_to_ratio),
        PrimitiveDesc::new("fixnum_to_float", 0, fixnum::fixnum_to_float),
        PrimitiveDesc::new("fixnum_to_string", 0, fixnum::fixnum_to_string),
        PrimitiveDesc::new(
            "fixnum_to_string_radix",
            1,
            fixnum::fixnum_to_string_radix,
        ),
        PrimitiveDesc::new("fixnum_eq", 1, fixnum::fixnum_eq),
        PrimitiveDesc::new("fixnum_ne", 1, fixnum::fixnum_ne),
        PrimitiveDesc::new("fixnum_lt", 1, fixnum::fixnum_lt),
        PrimitiveDesc::new("fixnum_le", 1, fixnum::fixnum_le),
        PrimitiveDesc::new("fixnum_gt", 1, fixnum::fixnum_gt),
        PrimitiveDesc::new("fixnum_ge", 1, fixnum::fixnum_ge),
        PrimitiveDesc::new("extend_with", 2, extend::extend_with),
        PrimitiveDesc::new("bignum_add", 1, bignum::bignum_add),
        PrimitiveDesc::new("bignum_sub", 1, bignum::bignum_sub),
        PrimitiveDesc::new("bignum_mul", 1, bignum::bignum_mul),
        PrimitiveDesc::new("bignum_div", 1, bignum::bignum_div),
        PrimitiveDesc::new("bignum_mod", 1, bignum::bignum_mod),
        PrimitiveDesc::new("bignum_neg", 0, bignum::bignum_neg),
        PrimitiveDesc::new("bignum_to_fixnum", 0, bignum::bignum_to_fixnum),
        PrimitiveDesc::new("bignum_to_ratio", 0, bignum::bignum_to_ratio),
        PrimitiveDesc::new("bignum_to_float", 0, bignum::bignum_to_float),
        PrimitiveDesc::new("bignum_to_string", 0, bignum::bignum_to_string),
        PrimitiveDesc::new("bignum_eq", 1, bignum::bignum_eq),
        PrimitiveDesc::new("bignum_ne", 1, bignum::bignum_ne),
        PrimitiveDesc::new("bignum_lt", 1, bignum::bignum_lt),
        PrimitiveDesc::new("bignum_le", 1, bignum::bignum_le),
        PrimitiveDesc::new("bignum_gt", 1, bignum::bignum_gt),
        PrimitiveDesc::new("bignum_ge", 1, bignum::bignum_ge),
        PrimitiveDesc::new("ratio_add", 1, ratio::ratio_add),
        PrimitiveDesc::new("ratio_sub", 1, ratio::ratio_sub),
        PrimitiveDesc::new("ratio_mul", 1, ratio::ratio_mul),
        PrimitiveDesc::new("ratio_div", 1, ratio::ratio_div),
        PrimitiveDesc::new("ratio_neg", 0, ratio::ratio_neg),
        PrimitiveDesc::new("ratio_numerator", 0, ratio::ratio_numerator),
        PrimitiveDesc::new("ratio_denominator", 0, ratio::ratio_denominator),
        PrimitiveDesc::new("ratio_to_fixnum", 0, ratio::ratio_to_fixnum),
        PrimitiveDesc::new("ratio_to_bignum", 0, ratio::ratio_to_bignum),
        PrimitiveDesc::new("ratio_to_float", 0, ratio::ratio_to_float),
        PrimitiveDesc::new("ratio_to_string", 0, ratio::ratio_to_string),
        PrimitiveDesc::new("ratio_eq", 1, ratio::ratio_eq),
        PrimitiveDesc::new("ratio_ne", 1, ratio::ratio_ne),
        PrimitiveDesc::new("ratio_lt", 1, ratio::ratio_lt),
        PrimitiveDesc::new("ratio_le", 1, ratio::ratio_le),
        PrimitiveDesc::new("ratio_gt", 1, ratio::ratio_gt),
        PrimitiveDesc::new("ratio_ge", 1, ratio::ratio_ge),
        PrimitiveDesc::new("float_add", 1, float::float_add),
        PrimitiveDesc::new("float_sub", 1, float::float_sub),
        PrimitiveDesc::new("float_mul", 1, float::float_mul),
        PrimitiveDesc::new("float_div", 1, float::float_div),
        PrimitiveDesc::new("float_mod", 1, float::float_mod),
        PrimitiveDesc::new("float_neg", 0, float::float_neg),
        PrimitiveDesc::new("float_sqrt", 0, float::float_sqrt),
        PrimitiveDesc::new("float_to_fixnum", 0, float::float_to_fixnum),
        PrimitiveDesc::new("float_to_bignum", 0, float::float_to_bignum),
        PrimitiveDesc::new("float_to_ratio", 0, float::float_to_ratio),
        PrimitiveDesc::new("float_to_string", 0, float::float_to_string),
        PrimitiveDesc::new(
            "float_to_string_digits",
            1,
            float::float_to_string_digits,
        ),
        PrimitiveDesc::new("float_eq", 1, float::float_eq),
        PrimitiveDesc::new("float_ne", 1, float::float_ne),
        PrimitiveDesc::new("float_lt", 1, float::float_lt),
        PrimitiveDesc::new("float_le", 1, float::float_le),
        PrimitiveDesc::new("float_gt", 1, float::float_gt),
        PrimitiveDesc::new("float_ge", 1, float::float_ge),
        PrimitiveDesc::new("float_approx_eq", 2, float::float_approx_eq),
        PrimitiveDesc::new("block_call0", 0, block::block_call0),
        PrimitiveDesc::new("block_call1", 1, block::block_call1),
        PrimitiveDesc::new("block_call2", 2, block::block_call2),
        PrimitiveDesc::new("block_call3", 3, block::block_call3),
        PrimitiveDesc::new("block_call4", 4, block::block_call4),
        PrimitiveDesc::new("block_call5", 5, block::block_call5),
        PrimitiveDesc::new("block_call6", 6, block::block_call6),
        PrimitiveDesc::new("block_call7", 7, block::block_call7),
        PrimitiveDesc::new("block_call8", 8, block::block_call8),
        PrimitiveDesc::new("array_size", 0, array::array_size),
        PrimitiveDesc::new(
            "array_clone_with_size",
            1,
            array::array_clone_with_size,
        ),
        PrimitiveDesc::new("array_at", 1, array::array_at),
        PrimitiveDesc::new("array_at_put", 2, array::array_at_put),
        PrimitiveDesc::new("string_print", 0, string::string_print),
        PrimitiveDesc::new("string_println", 0, string::string_println),
        PrimitiveDesc::new("string_length", 0, string::string_length),
        PrimitiveDesc::new(
            "string_to_bytearray",
            0,
            string::string_to_bytearray,
        ),
        PrimitiveDesc::new("string_to_symbol", 0, string::string_to_symbol),
        PrimitiveDesc::new("symbol_to_string", 0, string::symbol_to_string),
        PrimitiveDesc::new("symbol_length", 0, string::symbol_length),
        PrimitiveDesc::new("symbol_eq", 1, string::symbol_eq),
        PrimitiveDesc::new("symbol_ne", 1, string::symbol_ne),
        PrimitiveDesc::new("bytearray_size", 0, bytearray::bytearray_size),
        PrimitiveDesc::new(
            "bytearray_clone_with_size",
            1,
            bytearray::bytearray_clone_with_size,
        ),
        PrimitiveDesc::new(
            "bytearray_memcopy",
            4,
            bytearray::bytearray_memcopy,
        ),
        PrimitiveDesc::new(
            "bytearray_memcopy_overlapping",
            4,
            bytearray::bytearray_memcopy_overlapping,
        ),
        PrimitiveDesc::new(
            "bytearray_to_string",
            0,
            bytearray::bytearray_to_string,
        ),
        PrimitiveDesc::new(
            "bytearray_read_u8",
            1,
            bytearray::bytearray_read_u8,
        ),
        PrimitiveDesc::new(
            "bytearray_read_i8",
            1,
            bytearray::bytearray_read_i8,
        ),
        PrimitiveDesc::new(
            "bytearray_read_u16",
            1,
            bytearray::bytearray_read_u16,
        ),
        PrimitiveDesc::new(
            "bytearray_read_i16",
            1,
            bytearray::bytearray_read_i16,
        ),
        PrimitiveDesc::new(
            "bytearray_read_u32",
            1,
            bytearray::bytearray_read_u32,
        ),
        PrimitiveDesc::new(
            "bytearray_read_i32",
            1,
            bytearray::bytearray_read_i32,
        ),
        PrimitiveDesc::new(
            "bytearray_read_u64",
            1,
            bytearray::bytearray_read_u64,
        ),
        PrimitiveDesc::new(
            "bytearray_read_i64",
            1,
            bytearray::bytearray_read_i64,
        ),
        PrimitiveDesc::new(
            "bytearray_read_f32",
            1,
            bytearray::bytearray_read_f32,
        ),
        PrimitiveDesc::new(
            "bytearray_read_f64",
            1,
            bytearray::bytearray_read_f64,
        ),
        PrimitiveDesc::new(
            "bytearray_read_pointer",
            1,
            bytearray::bytearray_read_pointer,
        ),
        PrimitiveDesc::new(
            "bytearray_write_u8",
            2,
            bytearray::bytearray_write_u8,
        ),
        PrimitiveDesc::new(
            "bytearray_write_i8",
            2,
            bytearray::bytearray_write_i8,
        ),
        PrimitiveDesc::new(
            "bytearray_write_u16",
            2,
            bytearray::bytearray_write_u16,
        ),
        PrimitiveDesc::new(
            "bytearray_write_i16",
            2,
            bytearray::bytearray_write_i16,
        ),
        PrimitiveDesc::new(
            "bytearray_write_u32",
            2,
            bytearray::bytearray_write_u32,
        ),
        PrimitiveDesc::new(
            "bytearray_write_i32",
            2,
            bytearray::bytearray_write_i32,
        ),
        PrimitiveDesc::new(
            "bytearray_write_u64",
            2,
            bytearray::bytearray_write_u64,
        ),
        PrimitiveDesc::new(
            "bytearray_write_i64",
            2,
            bytearray::bytearray_write_i64,
        ),
        PrimitiveDesc::new(
            "bytearray_write_f32",
            2,
            bytearray::bytearray_write_f32,
        ),
        PrimitiveDesc::new(
            "bytearray_write_f64",
            2,
            bytearray::bytearray_write_f64,
        ),
        PrimitiveDesc::new(
            "bytearray_write_pointer",
            2,
            bytearray::bytearray_write_pointer,
        ),
        PrimitiveDesc::new("alien_new", 1, alien::alien_new),
        PrimitiveDesc::new("alien_from_address", 2, alien::alien_from_address),
        PrimitiveDesc::new("alien_free", 0, alien::alien_free),
        PrimitiveDesc::new("alien_size", 0, alien::alien_size),
        PrimitiveDesc::new("alien_address", 0, alien::alien_address),
        PrimitiveDesc::new("alien_is_null", 0, alien::alien_is_null),
        PrimitiveDesc::new("alien_read_u8", 1, alien::alien_read_u8),
        PrimitiveDesc::new("alien_read_i8", 1, alien::alien_read_i8),
        PrimitiveDesc::new("alien_read_u16", 1, alien::alien_read_u16),
        PrimitiveDesc::new("alien_read_i16", 1, alien::alien_read_i16),
        PrimitiveDesc::new("alien_read_u32", 1, alien::alien_read_u32),
        PrimitiveDesc::new("alien_read_i32", 1, alien::alien_read_i32),
        PrimitiveDesc::new("alien_read_u64", 1, alien::alien_read_u64),
        PrimitiveDesc::new("alien_read_i64", 1, alien::alien_read_i64),
        PrimitiveDesc::new("alien_read_f32", 1, alien::alien_read_f32),
        PrimitiveDesc::new("alien_read_f64", 1, alien::alien_read_f64),
        PrimitiveDesc::new("alien_read_pointer", 1, alien::alien_read_pointer),
        PrimitiveDesc::new("alien_write_u8", 2, alien::alien_write_u8),
        PrimitiveDesc::new("alien_write_i8", 2, alien::alien_write_i8),
        PrimitiveDesc::new("alien_write_u16", 2, alien::alien_write_u16),
        PrimitiveDesc::new("alien_write_i16", 2, alien::alien_write_i16),
        PrimitiveDesc::new("alien_write_u32", 2, alien::alien_write_u32),
        PrimitiveDesc::new("alien_write_i32", 2, alien::alien_write_i32),
        PrimitiveDesc::new("alien_write_u64", 2, alien::alien_write_u64),
        PrimitiveDesc::new("alien_write_i64", 2, alien::alien_write_i64),
        PrimitiveDesc::new("alien_write_f32", 2, alien::alien_write_f32),
        PrimitiveDesc::new("alien_write_f64", 2, alien::alien_write_f64),
        PrimitiveDesc::new(
            "alien_write_pointer",
            2,
            alien::alien_write_pointer,
        ),
        PrimitiveDesc::new(
            "alien_copy_to_bytearray",
            3,
            alien::alien_copy_to_bytearray,
        ),
        PrimitiveDesc::new(
            "alien_copy_from_bytearray",
            3,
            alien::alien_copy_from_bytearray,
        ),
        PrimitiveDesc::new("alien_library_open", 1, alien::alien_library_open),
        PrimitiveDesc::new("alien_library_sym", 1, alien::alien_library_sym),
        PrimitiveDesc::new(
            "alien_library_close",
            0,
            alien::alien_library_close,
        ),
        PrimitiveDesc::new(
            "alien_call_with_types",
            3,
            alien::alien_call_with_types,
        ),
        PrimitiveDesc::new("object_pin", 1, pin::object_pin),
        PrimitiveDesc::new("object_unpin", 1, pin::object_unpin),
        PrimitiveDesc::new("object_is_pinned", 1, pin::object_is_pinned),
        PrimitiveDesc::new("object_clone", 1, object_clone::object_clone),
        PrimitiveDesc::new("object_eq", 1, object_clone::object_eq),
        PrimitiveDesc::new("object_ne", 1, object_clone::object_ne),
        PrimitiveDesc::new(
            "object_become_with",
            2,
            r#become::object_become_with,
        ),
        PrimitiveDesc::new("object_reflect", 1, mirror::object_reflect),
        PrimitiveDesc::new("ctype_build_struct", 1, alien::ctype_build_struct),
        PrimitiveDesc::new(
            "ctype_field_info_at",
            1,
            alien::ctype_field_info_at,
        ),
        PrimitiveDesc::new("ctype_scalar_tag", 0, alien::ctype_scalar_tag),
        PrimitiveDesc::new("mirror_slot_count", 0, mirror::mirror_slot_count),
        PrimitiveDesc::new(
            "mirror_slot_name_at",
            1,
            mirror::mirror_slot_name_at,
        ),
        PrimitiveDesc::new("mirror_at", 1, mirror::mirror_at),
        PrimitiveDesc::new("mirror_at_put", 2, mirror::mirror_at_put),
        PrimitiveDesc::new(
            "mirror_is_parent_at",
            1,
            mirror::mirror_is_parent_at,
        ),
        PrimitiveDesc::new(
            "mirror_is_assignable_at",
            1,
            mirror::mirror_is_assignable_at,
        ),
        PrimitiveDesc::new(
            "mirror_add_slot_value",
            2,
            mirror::mirror_add_slot_value,
        ),
        PrimitiveDesc::new("mirror_remove_slot", 1, mirror::mirror_remove_slot),
        PrimitiveDesc::new("vm_eval", 1, vm::vm_eval),
        PrimitiveDesc::new("vm_module_open", 1, vm::vm_module_open),
        PrimitiveDesc::new("vm_module_use", 1, vm::vm_module_use),
        PrimitiveDesc::new("vm_module_use_as", 2, vm::vm_module_use_as),
        PrimitiveDesc::new("vm_module_use_only", 2, vm::vm_module_use_only),
        PrimitiveDesc::new("vm_module_export", 1, vm::vm_module_export),
        PrimitiveDesc::new("vm_module_at", 1, vm::vm_module_at),
        PrimitiveDesc::new("vm_current_module", 0, vm::vm_current_module),
        PrimitiveDesc::new("vm_platform_os", 0, vm::vm_platform_os),
        PrimitiveDesc::new("vm_platform_arch", 0, vm::vm_platform_arch),
        PrimitiveDesc::new("vm_with_handler_do", 2, vm::vm_with_handler_do),
        PrimitiveDesc::new("vm_signal", 1, vm::vm_signal),
        PrimitiveDesc::new("vm_unwind", 1, vm::vm_unwind),
        PrimitiveDesc::new("vm_then_do", 2, vm::vm_then_do),
    ]
}

pub fn primitive_index_by_name(
    prims: &[PrimitiveDesc],
    name: &str,
) -> Option<usize> {
    prims.iter().position(|p| p.name == name)
}

pub(crate) fn expect_fixnum(value: Value) -> Result<i64, RuntimeError> {
    if !value.is_fixnum() {
        return Err(RuntimeError::TypeError {
            expected: "fixnum",
            got: value,
        });
    }
    Ok(unsafe { value.to_i64() })
}

pub(crate) fn expect_bignum(
    value: Value,
) -> Result<*const BigNum, RuntimeError> {
    if !value.is_ref() {
        return Err(RuntimeError::TypeError {
            expected: "bignum",
            got: value,
        });
    }
    let header: &Header = unsafe { value.as_ref() };
    if header.object_type() != ObjectType::BigNum {
        return Err(RuntimeError::TypeError {
            expected: "bignum",
            got: value,
        });
    }
    Ok(value.ref_bits() as *const BigNum)
}

pub(crate) fn expect_ratio(value: Value) -> Result<*const Ratio, RuntimeError> {
    if !value.is_ref() {
        return Err(RuntimeError::TypeError {
            expected: "ratio",
            got: value,
        });
    }
    let header: &Header = unsafe { value.as_ref() };
    if header.object_type() != ObjectType::Ratio {
        return Err(RuntimeError::TypeError {
            expected: "ratio",
            got: value,
        });
    }
    Ok(value.ref_bits() as *const Ratio)
}

pub(crate) fn expect_float(value: Value) -> Result<*const Float, RuntimeError> {
    if !value.is_ref() {
        return Err(RuntimeError::TypeError {
            expected: "float",
            got: value,
        });
    }
    let header: &Header = unsafe { value.as_ref() };
    if header.object_type() != ObjectType::Float {
        return Err(RuntimeError::TypeError {
            expected: "float",
            got: value,
        });
    }
    Ok(value.ref_bits() as *const Float)
}

pub(crate) fn expect_string(
    value: Value,
) -> Result<*const object::VMString, RuntimeError> {
    if !value.is_ref() {
        return Err(RuntimeError::TypeError {
            expected: "string",
            got: value,
        });
    }
    let header: &Header = unsafe { value.as_ref() };
    if header.object_type() != ObjectType::Str {
        return Err(RuntimeError::TypeError {
            expected: "string",
            got: value,
        });
    }
    Ok(value.ref_bits() as *const object::VMString)
}

pub(crate) fn expect_symbol(
    value: Value,
) -> Result<*const object::VMSymbol, RuntimeError> {
    if !value.is_ref() {
        return Err(RuntimeError::TypeError {
            expected: "symbol",
            got: value,
        });
    }
    let header: &Header = unsafe { value.as_ref() };
    if header.object_type() != ObjectType::Symbol {
        return Err(RuntimeError::TypeError {
            expected: "symbol",
            got: value,
        });
    }
    Ok(value.ref_bits() as *const object::VMSymbol)
}

pub(crate) fn expect_bytearray(
    value: Value,
) -> Result<*const object::ByteArray, RuntimeError> {
    if !value.is_ref() {
        return Err(RuntimeError::TypeError {
            expected: "bytearray",
            got: value,
        });
    }
    let header: &Header = unsafe { value.as_ref() };
    if header.object_type() != ObjectType::ByteArray {
        return Err(RuntimeError::TypeError {
            expected: "bytearray",
            got: value,
        });
    }
    Ok(value.ref_bits() as *const object::ByteArray)
}

pub(crate) fn expect_array(value: Value) -> Result<*const Array, RuntimeError> {
    if !value.is_ref() {
        return Err(RuntimeError::TypeError {
            expected: "array",
            got: value,
        });
    }
    let header: &Header = unsafe { value.as_ref() };
    if header.object_type() != ObjectType::Array {
        return Err(RuntimeError::TypeError {
            expected: "array",
            got: value,
        });
    }
    Ok(value.ref_bits() as *const Array)
}

pub(crate) fn expect_alien(value: Value) -> Result<*const Alien, RuntimeError> {
    if !value.is_ref() {
        return Err(RuntimeError::TypeError {
            expected: "alien",
            got: value,
        });
    }
    let header: &Header = unsafe { value.as_ref() };
    if header.object_type() != ObjectType::Alien {
        return Err(RuntimeError::TypeError {
            expected: "alien",
            got: value,
        });
    }
    Ok(value.ref_bits() as *const Alien)
}

pub(crate) fn bool_value(vm: &VM, value: bool) -> Value {
    if value {
        vm.special.true_obj
    } else {
        vm.special.false_obj
    }
}
