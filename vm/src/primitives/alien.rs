use std::cell::RefCell;
use std::collections::HashMap;
use std::ffi::CString;
use std::mem::{align_of, size_of};

use libffi::middle::{Arg, Cif, CodePtr, Type};
use libffi::raw;
use object::{
    Alien, BigNum, ByteArray, MapFlags, ObjectType, Slot, SlotFlags,
    SlotObject, VMString, VMSymbol, Value,
};

use crate::alloc::{
    alloc_alien, alloc_bignum_from_i128, alloc_byte_array, alloc_float,
    alloc_map, alloc_slot_object,
};
use crate::interpreter::{with_roots, InterpreterState, RuntimeError};
use crate::primitives::string::intern_symbol;
use crate::primitives::{
    expect_alien, expect_array, expect_bignum, expect_bytearray, expect_fixnum,
    expect_float, expect_string, expect_symbol,
};
use crate::VM;

thread_local! {
    static TLS_CIF_CACHE: RefCell<HashMap<CifCacheKey, Cif>> = RefCell::new(HashMap::new());
}

fn with_thread_local_cif<R, FBuild, FUse>(
    key: CifCacheKey,
    build: FBuild,
    use_cif: FUse,
) -> R
where
    FBuild: FnOnce() -> Cif,
    FUse: FnOnce(&Cif) -> R,
{
    TLS_CIF_CACHE.with(|cache| {
        let mut map = cache.borrow_mut();
        let cif = map.entry(key).or_insert_with(build);
        use_cif(cif)
    })
}

extern "C" {
    fn malloc(size: usize) -> *mut u8;
    fn free(ptr: *mut u8);
}

#[cfg(target_family = "unix")]
#[link(name = "dl")]
extern "C" {
    fn dlopen(filename: *const i8, flag: i32) -> *mut u8;
    fn dlsym(handle: *mut u8, symbol: *const i8) -> *mut u8;
    fn dlclose(handle: *mut u8) -> i32;
}

#[cfg(target_os = "windows")]
extern "system" {
    fn LoadLibraryA(lpLibFileName: *const i8) -> *mut u8;
    fn GetProcAddress(hModule: *mut u8, lpProcName: *const i8) -> *mut u8;
    fn FreeLibrary(hLibModule: *mut u8) -> i32;
}

fn alien_ptr(receiver: Value) -> Result<(*mut Alien, u64), RuntimeError> {
    let ptr = expect_alien(receiver)? as *mut Alien;
    let addr = unsafe { (*ptr).ptr };
    Ok((ptr, addr))
}

fn check_bounds(
    addr: u64,
    offset: i64,
    size: usize,
) -> Result<*mut u8, RuntimeError> {
    if addr == 0 {
        return Err(RuntimeError::Unimplemented {
            message: "alien pointer is null",
        });
    }
    if offset < 0 {
        return Err(RuntimeError::Unimplemented {
            message: "alien offset must be non-negative",
        });
    }
    Ok(unsafe { (addr as *mut u8).add(offset as usize).add(size).sub(size) })
}

fn get_offset(args: &[Value], idx: usize) -> Result<i64, RuntimeError> {
    let v = args.get(idx).copied().ok_or(RuntimeError::TypeError {
        expected: "offset",
        got: Value::from_i64(0),
    })?;
    expect_fixnum(v)
}

fn output_i64(
    vm: &mut VM,
    state: &mut InterpreterState,
    roots: &mut Vec<Value>,
    value: i64,
) -> Value {
    if (-((1_i64) << 62)..=((1_i64 << 62) - 1)).contains(&value) {
        return Value::from_i64(value);
    }
    with_roots(vm, state, roots, |proxy, root_provider| unsafe {
        alloc_bignum_from_i128(proxy, root_provider, value as i128).value()
    })
}

fn output_u64(
    vm: &mut VM,
    state: &mut InterpreterState,
    roots: &mut Vec<Value>,
    value: u64,
) -> Value {
    if value <= BigNum::FIXNUM_MAX as u64 {
        return Value::from_i64(value as i64);
    }
    with_roots(vm, state, roots, |proxy, root_provider| unsafe {
        alloc_bignum_from_i128(proxy, root_provider, value as i128).value()
    })
}

fn value_to_i64(value: Value) -> Result<i64, RuntimeError> {
    if value.is_fixnum() {
        return expect_fixnum(value);
    }

    let bn_ptr = expect_bignum(value)?;
    let bn = unsafe { &*bn_ptr };
    match (bn.sign, bn.len()) {
        (0, _) => Ok(0),
        (1, 1) => {
            let limb = bn.limbs()[0];
            if limb <= i64::MAX as u64 {
                Ok(limb as i64)
            } else {
                Err(RuntimeError::Unimplemented {
                    message: "integer out of i64 range",
                })
            }
        }
        (-1, 1) => {
            let limb = bn.limbs()[0];
            if limb == (1_u64 << 63) {
                Ok(i64::MIN)
            } else if limb < (1_u64 << 63) {
                Ok(-(limb as i64))
            } else {
                Err(RuntimeError::Unimplemented {
                    message: "integer out of i64 range",
                })
            }
        }
        _ => Err(RuntimeError::Unimplemented {
            message: "integer out of i64 range",
        }),
    }
}

fn value_to_u64(value: Value) -> Result<u64, RuntimeError> {
    if value.is_fixnum() {
        let n = expect_fixnum(value)?;
        if n < 0 {
            return Err(RuntimeError::Unimplemented {
                message: "integer out of u64 range",
            });
        }
        return Ok(n as u64);
    }

    let bn_ptr = expect_bignum(value)?;
    let bn = unsafe { &*bn_ptr };
    match (bn.sign, bn.len()) {
        (0, _) => Ok(0),
        (1, 1) => Ok(bn.limbs()[0]),
        _ => Err(RuntimeError::Unimplemented {
            message: "integer out of u64 range",
        }),
    }
}

fn value_to_pointer_bits(value: Value) -> Result<u64, RuntimeError> {
    if value.raw() == 0 {
        return Ok(0);
    }
    if value.is_fixnum() {
        let n = expect_fixnum(value)?;
        if n < 0 {
            return Err(RuntimeError::Unimplemented {
                message: "pointer must be non-negative",
            });
        }
        return Ok(n as u64);
    }
    if value.is_ref() {
        let header: &object::Header = unsafe { value.as_ref() };
        match header.object_type() {
            ObjectType::Alien => {
                let ptr = expect_alien(value)?;
                return Ok(unsafe { (*ptr).ptr });
            }
            ObjectType::ByteArray => {
                let ba = expect_bytearray(value)?;
                let p = unsafe { (ba as *const ByteArray).add(1) as *const u8 };
                return Ok(p as u64);
            }
            ObjectType::Str => {
                let s = expect_string(value)?;
                let ba_val = unsafe { (*s).data };
                let ba_ptr = expect_bytearray(ba_val)?;
                let p =
                    unsafe { (ba_ptr as *const ByteArray).add(1) as *const u8 };
                return Ok(p as u64);
            }
            ObjectType::Symbol => {
                let s = expect_symbol(value)?;
                let ba_val = unsafe { (*s).data };
                let ba_ptr = expect_bytearray(ba_val)?;
                let p =
                    unsafe { (ba_ptr as *const ByteArray).add(1) as *const u8 };
                return Ok(p as u64);
            }
            _ => {}
        }
    }

    Err(RuntimeError::TypeError {
        expected: "pointer-compatible value",
        got: value,
    })
}

// ── Constructors ─────────────────────────────────────────────────────

pub fn alien_new(
    vm: &mut VM,
    state: &mut InterpreterState,
    _receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let size_val = args.get(0).copied().ok_or(RuntimeError::TypeError {
        expected: "size",
        got: Value::from_i64(0),
    })?;
    let size = expect_fixnum(size_val)?;
    if size < 0 {
        return Err(RuntimeError::Unimplemented {
            message: "alien size must be non-negative",
        });
    }
    let c_ptr = if size == 0 {
        0u64
    } else {
        let p = unsafe { malloc(size as usize) };
        if p.is_null() {
            return Err(RuntimeError::Unimplemented {
                message: "malloc failed",
            });
        }
        unsafe { p.write_bytes(0, size as usize) };
        p as u64
    };
    let mut scratch = Vec::new();
    let alien = with_roots(vm, state, &mut scratch, |proxy, roots| unsafe {
        alloc_alien(proxy, roots, c_ptr, size as u64).value()
    });
    Ok(alien)
}

pub fn alien_from_address(
    vm: &mut VM,
    state: &mut InterpreterState,
    _receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let addr_val = args.get(0).copied().ok_or(RuntimeError::TypeError {
        expected: "address",
        got: Value::from_i64(0),
    })?;
    let size_val = args.get(1).copied().ok_or(RuntimeError::TypeError {
        expected: "size",
        got: Value::from_i64(0),
    })?;
    let addr = expect_fixnum(addr_val)? as u64;
    let size = expect_fixnum(size_val)? as u64;
    let mut scratch = Vec::new();
    let alien = with_roots(vm, state, &mut scratch, |proxy, roots| unsafe {
        alloc_alien(proxy, roots, addr, size).value()
    });
    Ok(alien)
}

pub fn alien_free(
    _vm: &mut VM,
    _state: &mut InterpreterState,
    receiver: Value,
    _args: &[Value],
) -> Result<Value, RuntimeError> {
    let ptr = expect_alien(receiver)? as *mut Alien;
    let addr = unsafe { (*ptr).ptr };
    if addr != 0 {
        unsafe { free(addr as *mut u8) };
        unsafe { (*ptr).ptr = 0 };
    }
    Ok(receiver)
}

pub fn alien_size(
    _vm: &mut VM,
    _state: &mut InterpreterState,
    receiver: Value,
    _args: &[Value],
) -> Result<Value, RuntimeError> {
    let ptr = expect_alien(receiver)?;
    Ok(Value::from_i64(unsafe { (*ptr).size } as i64))
}

pub fn alien_address(
    _vm: &mut VM,
    _state: &mut InterpreterState,
    receiver: Value,
    _args: &[Value],
) -> Result<Value, RuntimeError> {
    let ptr = expect_alien(receiver)?;
    Ok(Value::from_i64(unsafe { (*ptr).ptr } as i64))
}

pub fn alien_is_null(
    vm: &mut VM,
    _state: &mut InterpreterState,
    receiver: Value,
    _args: &[Value],
) -> Result<Value, RuntimeError> {
    let ptr = expect_alien(receiver)?;
    let is_null = unsafe { (*ptr).ptr } == 0;
    Ok(if is_null {
        vm.special.true_obj
    } else {
        vm.special.false_obj
    })
}

macro_rules! alien_read_int {
    ($name:ident, $ty:ty) => {
        pub fn $name(
            _vm: &mut VM,
            _state: &mut InterpreterState,
            receiver: Value,
            args: &[Value],
        ) -> Result<Value, RuntimeError> {
            let offset = get_offset(args, 0)?;
            let (_, addr) = alien_ptr(receiver)?;
            let p = check_bounds(addr, offset, size_of::<$ty>())?;
            let val = unsafe { (p as *const $ty).read_unaligned() } as i64;
            Ok(Value::from_i64(val))
        }
    };
}

alien_read_int!(alien_read_u8, u8);
alien_read_int!(alien_read_i8, i8);
alien_read_int!(alien_read_u16, u16);
alien_read_int!(alien_read_i16, i16);
alien_read_int!(alien_read_u32, u32);
alien_read_int!(alien_read_i32, i32);

pub fn alien_read_i64(
    vm: &mut VM,
    state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let offset = get_offset(args, 0)?;
    let (_, addr) = alien_ptr(receiver)?;
    let p = check_bounds(addr, offset, 8)?;
    let val = unsafe { (p as *const i64).read_unaligned() };
    let mut scratch = vec![receiver];
    Ok(output_i64(vm, state, &mut scratch, val))
}

pub fn alien_read_u64(
    vm: &mut VM,
    state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let offset = get_offset(args, 0)?;
    let (_, addr) = alien_ptr(receiver)?;
    let p = check_bounds(addr, offset, 8)?;
    let val = unsafe { (p as *const u64).read_unaligned() };
    let mut scratch = vec![receiver];
    Ok(output_u64(vm, state, &mut scratch, val))
}

pub fn alien_read_f32(
    vm: &mut VM,
    state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let offset = get_offset(args, 0)?;
    let (_, addr) = alien_ptr(receiver)?;
    let p = check_bounds(addr, offset, 4)?;
    let val = unsafe { (p as *const f32).read_unaligned() } as f64;
    let mut scratch = vec![receiver];
    let float = with_roots(vm, state, &mut scratch, |proxy, roots| unsafe {
        alloc_float(proxy, roots, val).value()
    });
    Ok(float)
}

pub fn alien_read_f64(
    vm: &mut VM,
    state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let offset = get_offset(args, 0)?;
    let (_, addr) = alien_ptr(receiver)?;
    let p = check_bounds(addr, offset, 8)?;
    let val = unsafe { (p as *const f64).read_unaligned() };
    let mut scratch = vec![receiver];
    let float = with_roots(vm, state, &mut scratch, |proxy, roots| unsafe {
        alloc_float(proxy, roots, val).value()
    });
    Ok(float)
}

pub fn alien_read_pointer(
    vm: &mut VM,
    state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let offset = get_offset(args, 0)?;
    let (_, addr) = alien_ptr(receiver)?;
    let p = check_bounds(addr, offset, 8)?;
    let ptr_val = unsafe { (p as *const u64).read_unaligned() };
    let mut scratch = vec![receiver];
    let alien = with_roots(vm, state, &mut scratch, |proxy, roots| unsafe {
        alloc_alien(proxy, roots, ptr_val, 0).value()
    });
    Ok(alien)
}

// ── Typed writes ─────────────────────────────────────────────────────

macro_rules! alien_write_int {
    ($name:ident, $ty:ty) => {
        pub fn $name(
            _vm: &mut VM,
            _state: &mut InterpreterState,
            receiver: Value,
            args: &[Value],
        ) -> Result<Value, RuntimeError> {
            let off_v =
                args.get(0).copied().ok_or(RuntimeError::TypeError {
                    expected: "offset",
                    got: Value::from_i64(0),
                })?;
            let value_v =
                args.get(1).copied().ok_or(RuntimeError::TypeError {
                    expected: "value",
                    got: Value::from_i64(0),
                })?;
            let offset = expect_fixnum(off_v)?;
            let val = expect_fixnum(value_v)? as $ty;
            let (_, addr) = alien_ptr(receiver)?;
            let p = check_bounds(addr, offset, size_of::<$ty>())?;
            unsafe { (p as *mut $ty).write_unaligned(val) };
            Ok(receiver)
        }
    };
}

alien_write_int!(alien_write_u8, u8);
alien_write_int!(alien_write_i8, i8);
alien_write_int!(alien_write_u16, u16);
alien_write_int!(alien_write_i16, i16);
alien_write_int!(alien_write_u32, u32);
alien_write_int!(alien_write_i32, i32);

pub fn alien_write_u64(
    _vm: &mut VM,
    _state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let off_v = args.get(0).copied().ok_or(RuntimeError::TypeError {
        expected: "offset",
        got: Value::from_i64(0),
    })?;
    let value_v = args.get(1).copied().ok_or(RuntimeError::TypeError {
        expected: "value",
        got: Value::from_i64(0),
    })?;
    let offset = expect_fixnum(off_v)?;
    let value = value_to_u64(value_v)?;
    let (_, addr) = alien_ptr(receiver)?;
    let p = check_bounds(addr, offset, size_of::<u64>())?;
    unsafe { (p as *mut u64).write_unaligned(value) };
    Ok(receiver)
}

pub fn alien_write_i64(
    _vm: &mut VM,
    _state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let off_v = args.get(0).copied().ok_or(RuntimeError::TypeError {
        expected: "offset",
        got: Value::from_i64(0),
    })?;
    let value_v = args.get(1).copied().ok_or(RuntimeError::TypeError {
        expected: "value",
        got: Value::from_i64(0),
    })?;
    let offset = expect_fixnum(off_v)?;
    let value = value_to_i64(value_v)?;
    let (_, addr) = alien_ptr(receiver)?;
    let p = check_bounds(addr, offset, size_of::<i64>())?;
    unsafe { (p as *mut i64).write_unaligned(value) };
    Ok(receiver)
}

pub fn alien_write_f32(
    _vm: &mut VM,
    _state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let off_v = args.get(0).copied().ok_or(RuntimeError::TypeError {
        expected: "offset",
        got: Value::from_i64(0),
    })?;
    let val_v = args.get(1).copied().ok_or(RuntimeError::TypeError {
        expected: "float value",
        got: Value::from_i64(0),
    })?;
    let offset = expect_fixnum(off_v)?;
    let val =
        unsafe { (*crate::primitives::expect_float(val_v)?).value } as f32;
    let (_, addr) = alien_ptr(receiver)?;
    let p = check_bounds(addr, offset, 4)?;
    unsafe { (p as *mut f32).write_unaligned(val) };
    Ok(receiver)
}

pub fn alien_write_f64(
    _vm: &mut VM,
    _state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let off_v = args.get(0).copied().ok_or(RuntimeError::TypeError {
        expected: "offset",
        got: Value::from_i64(0),
    })?;
    let val_v = args.get(1).copied().ok_or(RuntimeError::TypeError {
        expected: "float value",
        got: Value::from_i64(0),
    })?;
    let offset = expect_fixnum(off_v)?;
    let val = unsafe { (*crate::primitives::expect_float(val_v)?).value };
    let (_, addr) = alien_ptr(receiver)?;
    let p = check_bounds(addr, offset, 8)?;
    unsafe { (p as *mut f64).write_unaligned(val) };
    Ok(receiver)
}

pub fn alien_write_pointer(
    _vm: &mut VM,
    _state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let off_v = args.get(0).copied().ok_or(RuntimeError::TypeError {
        expected: "offset",
        got: Value::from_i64(0),
    })?;
    let val_v = args.get(1).copied().ok_or(RuntimeError::TypeError {
        expected: "pointer value",
        got: Value::from_i64(0),
    })?;
    let offset = expect_fixnum(off_v)?;
    // Accept fixnum (raw address) or Alien (use ptr field)
    let ptr_bits: u64 = if val_v.is_fixnum() {
        expect_fixnum(val_v)? as u64
    } else {
        let a = expect_alien(val_v)?;
        unsafe { (*a).ptr }
    };
    let (_, addr) = alien_ptr(receiver)?;
    let p = check_bounds(addr, offset, 8)?;
    unsafe { (p as *mut u64).write_unaligned(ptr_bits) };
    Ok(receiver)
}

const CTYPE_TAG_VOID: i64 = 1;
const CTYPE_TAG_I8: i64 = 2;
const CTYPE_TAG_U8: i64 = 3;
const CTYPE_TAG_I16: i64 = 4;
const CTYPE_TAG_U16: i64 = 5;
const CTYPE_TAG_I32: i64 = 6;
const CTYPE_TAG_U32: i64 = 7;
const CTYPE_TAG_I64: i64 = 8;
const CTYPE_TAG_U64: i64 = 9;
const CTYPE_TAG_F32: i64 = 10;
const CTYPE_TAG_F64: i64 = 11;
const CTYPE_TAG_POINTER: i64 = 12;
const CTYPE_TAG_SIZE: i64 = 13;

#[derive(Clone, Copy)]
enum CTypeKind {
    Void,
    I8,
    U8,
    I16,
    U16,
    I32,
    U32,
    I64,
    U64,
    F32,
    F64,
    Pointer,
    Size,
    Struct,
}

impl CTypeKind {
    fn from_tag(tag: i64) -> Option<Self> {
        match tag {
            CTYPE_TAG_VOID => Some(Self::Void),
            CTYPE_TAG_I8 => Some(Self::I8),
            CTYPE_TAG_U8 => Some(Self::U8),
            CTYPE_TAG_I16 => Some(Self::I16),
            CTYPE_TAG_U16 => Some(Self::U16),
            CTYPE_TAG_I32 => Some(Self::I32),
            CTYPE_TAG_U32 => Some(Self::U32),
            CTYPE_TAG_I64 => Some(Self::I64),
            CTYPE_TAG_U64 => Some(Self::U64),
            CTYPE_TAG_F32 => Some(Self::F32),
            CTYPE_TAG_F64 => Some(Self::F64),
            CTYPE_TAG_POINTER => Some(Self::Pointer),
            CTYPE_TAG_SIZE => Some(Self::Size),
            _ => None,
        }
    }

    fn ffi_type(self) -> Type {
        match self {
            Self::Void => Type::void(),
            Self::I8 => Type::i8(),
            Self::U8 => Type::u8(),
            Self::I16 => Type::i16(),
            Self::U16 => Type::u16(),
            Self::I32 => Type::i32(),
            Self::U32 => Type::u32(),
            Self::I64 => Type::i64(),
            Self::U64 => Type::u64(),
            Self::F32 => Type::f32(),
            Self::F64 => Type::f64(),
            Self::Pointer => Type::pointer(),
            Self::Size => Type::usize(),
            Self::Struct => {
                unreachable!("struct ffi type comes from field layout")
            }
        }
    }

    fn scalar_tag(self) -> Option<i64> {
        match self {
            Self::Void => Some(CTYPE_TAG_VOID),
            Self::I8 => Some(CTYPE_TAG_I8),
            Self::U8 => Some(CTYPE_TAG_U8),
            Self::I16 => Some(CTYPE_TAG_I16),
            Self::U16 => Some(CTYPE_TAG_U16),
            Self::I32 => Some(CTYPE_TAG_I32),
            Self::U32 => Some(CTYPE_TAG_U32),
            Self::I64 => Some(CTYPE_TAG_I64),
            Self::U64 => Some(CTYPE_TAG_U64),
            Self::F32 => Some(CTYPE_TAG_F32),
            Self::F64 => Some(CTYPE_TAG_F64),
            Self::Pointer => Some(CTYPE_TAG_POINTER),
            Self::Size => Some(CTYPE_TAG_SIZE),
            Self::Struct => None,
        }
    }
}

#[derive(Clone)]
struct CTypeDescriptor {
    kind: CTypeKind,
    ffi_type: Type,
    size: usize,
    #[allow(dead_code)]
    align: usize,
    fields: Vec<CTypeField>,
}

#[derive(Clone, Copy)]
struct CTypeField {
    name: Value,
    offset: usize,
    descriptor: Value,
}

struct CTypeCache {
    magic: u64,
    kind: CTypeKind,
    ffi_type: Type,
    size: usize,
    #[allow(dead_code)]
    align: usize,
    fields: Vec<CTypeField>,
}

const CTYPE_CACHE_MAGIC: u64 = 0x4354_5950_455f_4348;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct CifCacheKey {
    fn_ptr: u64,
    param_types: Vec<u64>,
    return_type: u64,
}

enum FfiArgValue {
    I8(i8),
    U8(u8),
    I16(i16),
    U16(u16),
    I32(i32),
    U32(u32),
    I64(i64),
    U64(u64),
    F32(f32),
    F64(f64),
    Pointer(usize),
    Size(usize),
    Struct(Vec<u8>),
}
fn slot_name(slot: &object::Slot) -> Result<&str, RuntimeError> {
    if !slot.name.is_ref() {
        return Err(RuntimeError::TypeError {
            expected: "slot name string",
            got: slot.name,
        });
    }
    let vm_str: &VMString = unsafe { slot.name.as_ref() };
    Ok(unsafe { vm_str.as_str() })
}

fn slot_current_value(
    obj: *mut SlotObject,
    slot: &object::Slot,
) -> Result<Value, RuntimeError> {
    if slot.is_constant() {
        return Ok(slot.value);
    }
    if slot.is_assignable() {
        if !slot.value.is_fixnum() {
            return Err(RuntimeError::Unimplemented {
                message: "assignable ctype slot offset is not fixnum",
            });
        }
        let offset = expect_fixnum(slot.value)?;
        if offset < 0 {
            return Err(RuntimeError::Unimplemented {
                message: "assignable slot offset must be non-negative",
            });
        }
        let value = unsafe { (*obj).read_value(offset as u32) };
        return Ok(value);
    }
    Err(RuntimeError::Unimplemented {
        message: "unsupported ctype slot kind",
    })
}

fn compute_struct_layout(
    field_types: &[Type],
) -> Result<(Type, usize, usize, Vec<usize>), RuntimeError> {
    let ffi_type = Type::structure(field_types.iter().cloned());
    let raw_type = ffi_type.as_raw_ptr();
    let mut offsets = vec![0usize; field_types.len()];
    let status = unsafe {
        raw::ffi_get_struct_offsets(
            raw::ffi_abi_FFI_DEFAULT_ABI,
            raw_type,
            offsets.as_mut_ptr(),
        )
    };
    if status != raw::ffi_status_FFI_OK {
        return Err(RuntimeError::Unimplemented {
            message: "failed to compute ctype struct layout",
        });
    }
    let size = unsafe { (*raw_type).size };
    let align = unsafe { (*raw_type).alignment } as usize;
    Ok((ffi_type, size, align, offsets))
}

fn bytearray_cache_ptr(value: Value) -> Option<*const CTypeCache> {
    if !value.is_ref() {
        return None;
    }
    let header: &object::Header = unsafe { value.as_ref() };
    if header.object_type() != ObjectType::ByteArray {
        return None;
    }
    let ba = value.ref_bits() as *const ByteArray;
    let len = unsafe { (*ba).len() as usize };
    if len != size_of::<CTypeCache>() {
        return None;
    }
    let data = unsafe { (ba as *const u8).add(size_of::<ByteArray>()) };
    if (data as usize) % align_of::<CTypeCache>() != 0 {
        return None;
    }
    Some(data as *const CTypeCache)
}

fn decode_cached_impl(impl_value: Value) -> Option<CTypeDescriptor> {
    if let Some(cache_ptr) = bytearray_cache_ptr(impl_value) {
        let cached = unsafe { &*cache_ptr };
        if cached.magic == CTYPE_CACHE_MAGIC {
            return Some(CTypeDescriptor {
                kind: cached.kind,
                ffi_type: cached.ffi_type.clone(),
                size: cached.size,
                align: cached.align,
                fields: cached.fields.clone(),
            });
        }
    }

    if impl_value.is_ref() {
        let impl_header: &object::Header = unsafe { impl_value.as_ref() };
        if impl_header.object_type() == object::ObjectType::Alien {
            let cached_alien = impl_value.ref_bits() as *const Alien;
            let cache_size = unsafe { (*cached_alien).size } as usize;
            if cache_size == size_of::<CTypeCache>() {
                let cache_ptr =
                    unsafe { (*cached_alien).ptr as *const CTypeCache };
                if !cache_ptr.is_null() {
                    let cached = unsafe { &*cache_ptr };
                    return Some(CTypeDescriptor {
                        kind: cached.kind,
                        ffi_type: cached.ffi_type.clone(),
                        size: cached.size,
                        align: cached.align,
                        fields: cached.fields.clone(),
                    });
                }
            }
        }
    }

    None
}

fn alloc_ctype_cache_value(
    vm: &mut VM,
    state: &mut InterpreterState,
    scratch: &mut Vec<Value>,
    cache: CTypeCache,
) -> Result<Value, RuntimeError> {
    let zero = vec![0u8; size_of::<CTypeCache>()];
    let cache_ba = with_roots(vm, state, scratch, |proxy, roots| unsafe {
        alloc_byte_array(proxy, roots, &zero).value()
    });
    let ba_ptr = expect_bytearray(cache_ba)? as *mut ByteArray;
    let data = unsafe { (ba_ptr as *mut u8).add(size_of::<ByteArray>()) };
    if (data as usize) % align_of::<CTypeCache>() != 0 {
        return Err(RuntimeError::Unimplemented {
            message: "bytearray cache alignment too small for CTypeCache",
        });
    }
    unsafe { (data as *mut CTypeCache).write(cache) };
    Ok(cache_ba)
}

fn has_ctype_parent(
    descriptor: Value,
    ctype_root: Value,
    seen: &mut Vec<u64>,
) -> Result<bool, RuntimeError> {
    if !descriptor.is_ref() {
        return Ok(false);
    }
    if seen.contains(&descriptor.raw()) {
        return Ok(false);
    }
    seen.push(descriptor.raw());

    let header: &object::Header = unsafe { descriptor.as_ref() };
    if header.object_type() != ObjectType::Slots {
        return Ok(false);
    }

    let obj = descriptor.ref_bits() as *mut SlotObject;
    let map: &object::Map = unsafe { (*obj).map.as_ref() };
    for slot in unsafe { map.slots() } {
        if !slot.is_parent() || slot.is_assignment() {
            continue;
        }
        let parent = slot_current_value(obj, slot)?;
        if parent.raw() == ctype_root.raw() {
            return Ok(true);
        }
        if has_ctype_parent(parent, ctype_root, seen)? {
            return Ok(true);
        }
    }
    Ok(false)
}

fn decode_ctype_descriptor(
    vm: &mut VM,
    state: &mut InterpreterState,
    descriptor: Value,
    scratch: &mut Vec<Value>,
    stack: &mut Vec<u64>,
) -> Result<CTypeDescriptor, RuntimeError> {
    if !descriptor.is_ref() {
        return Err(RuntimeError::TypeError {
            expected: "ctype descriptor object",
            got: descriptor,
        });
    }

    if descriptor.raw() == vm.special.none.raw() {
        return Err(RuntimeError::Unimplemented {
            message: "ctype descriptor is None",
        });
    }

    let header: &object::Header = unsafe { descriptor.as_ref() };
    if header.object_type() != object::ObjectType::Slots {
        return Err(RuntimeError::TypeError {
            expected: "ctype descriptor object",
            got: descriptor,
        });
    }

    if stack.contains(&descriptor.raw()) {
        return Err(RuntimeError::Unimplemented {
            message: "ctype descriptor recursion cycle",
        });
    }
    stack.push(descriptor.raw());

    let obj = descriptor.ref_bits() as *mut SlotObject;
    let map: &object::Map = unsafe { (*obj).map.as_ref() };
    let mut logical_slots = Vec::new();
    for slot in unsafe { map.slots() } {
        if slot.is_parent() || slot.is_assignment() {
            continue;
        }
        logical_slots.push(*slot);
    }

    if logical_slots.len() < 3 {
        let message = if map.slot_count() == 0 {
            "ctype descriptor map has no slots"
        } else {
            "ctype descriptor requires impl, size, align slots"
        };
        stack.pop();
        return Err(RuntimeError::Unimplemented { message });
    }

    if slot_name(&logical_slots[0])? != "impl"
        || slot_name(&logical_slots[1])? != "size"
        || slot_name(&logical_slots[2])? != "align"
    {
        stack.pop();
        return Err(RuntimeError::Unimplemented {
            message: "ctype descriptor slot order must be impl,size,align",
        });
    }

    let impl_slot = logical_slots[0];
    let impl_value = slot_current_value(obj, &impl_slot)?;

    if let Some(cached_desc) = decode_cached_impl(impl_value) {
        stack.pop();
        return Ok(cached_desc);
    }

    let size_value = slot_current_value(obj, &logical_slots[1])?;
    let align_value = slot_current_value(obj, &logical_slots[2])?;
    if !size_value.is_fixnum() {
        stack.pop();
        return Err(RuntimeError::Unimplemented {
            message: "ctype size slot is not fixnum",
        });
    }
    if !align_value.is_fixnum() {
        stack.pop();
        return Err(RuntimeError::Unimplemented {
            message: "ctype align slot is not fixnum",
        });
    }
    let slot_size = expect_fixnum(size_value)?;
    let slot_align = expect_fixnum(align_value)?;
    if slot_size < 0 || slot_align <= 0 {
        stack.pop();
        return Err(RuntimeError::Unimplemented {
            message: "ctype descriptor size/align must be non-negative",
        });
    }

    let field_slots: Vec<object::Slot> = logical_slots[3..]
        .iter()
        .copied()
        .filter(|slot| {
            !value_is_method_object(slot.value)
                && slot_name(slot)
                    .map(|name| !name.ends_with(':'))
                    .unwrap_or(true)
        })
        .collect();
    let (kind, ffi_type, size, align, fields) = if impl_value.is_fixnum() {
        if !field_slots.is_empty() {
            stack.pop();
            return Err(RuntimeError::Unimplemented {
                message: "scalar ctype descriptor cannot define fields",
            });
        }
        let tag = expect_fixnum(impl_value)?;
        let kind =
            CTypeKind::from_tag(tag).ok_or(RuntimeError::Unimplemented {
                message: "unknown scalar ctype tag",
            })?;
        (
            kind,
            kind.ffi_type(),
            slot_size as usize,
            slot_align as usize,
            Vec::new(),
        )
    } else if impl_value.raw() == vm.special.none.raw() {
        let mut field_types = Vec::with_capacity(field_slots.len());
        let mut field_desc_values = Vec::with_capacity(field_slots.len());
        for field_slot in &field_slots {
            let field_desc_value = slot_current_value(obj, field_slot)?;
            let field_desc = decode_ctype_descriptor(
                vm,
                state,
                field_desc_value,
                scratch,
                stack,
            )?;
            field_types.push(field_desc.ffi_type);
            field_desc_values.push(field_desc_value);
        }
        let (ffi_type, size, align, offsets) =
            compute_struct_layout(&field_types)?;
        let mut fields = Vec::with_capacity(field_slots.len());
        for (i, field_slot) in field_slots.iter().enumerate() {
            fields.push(CTypeField {
                name: field_slot.name,
                offset: offsets[i],
                descriptor: field_desc_values[i],
            });
        }
        (CTypeKind::Struct, ffi_type, size, align, fields)
    } else {
        stack.pop();
        return Err(RuntimeError::Unimplemented {
            message:
                "ctype descriptor impl must be fixnum tag, None, or cached impl",
        });
    };

    let cache = CTypeCache {
        magic: CTYPE_CACHE_MAGIC,
        kind,
        ffi_type: ffi_type.clone(),
        size,
        align,
        fields: fields.clone(),
    };
    let cache_value = alloc_ctype_cache_value(vm, state, scratch, cache)?;

    if impl_slot.is_assignable() {
        if !impl_slot.value.is_fixnum() {
            stack.pop();
            return Err(RuntimeError::Unimplemented {
                message: "ctype impl slot metadata offset is not fixnum",
            });
        }
        let impl_offset = expect_fixnum(impl_slot.value)?;
        unsafe { (*obj).write_value(impl_offset as u32, cache_value) };
        vm.heap_proxy.write_barrier(descriptor, cache_value);
    }

    stack.pop();
    Ok(CTypeDescriptor {
        kind,
        ffi_type,
        size,
        align,
        fields,
    })
}

pub fn ctype_build_struct(
    vm: &mut VM,
    state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let definition = args.get(0).copied().ok_or(RuntimeError::TypeError {
        expected: "ctype struct field definition",
        got: Value::from_i64(0),
    })?;
    let def_obj = expect_slot_object_ptr(definition)?;
    let def_map: &object::Map = unsafe { (*def_obj).map.as_ref() };

    let mut field_names = Vec::new();
    let mut field_values = Vec::new();
    let mut field_types = Vec::new();
    let mut decode_stack = Vec::new();
    let mut seen = Vec::new();
    let mut scratch = vec![receiver, definition];

    for slot in unsafe { def_map.slots() } {
        if slot.is_parent() || slot.is_assignment() {
            continue;
        }
        let name = slot_name(slot)?;
        if name == "impl" || name == "size" || name == "align" {
            continue;
        }

        let field_desc = slot_current_value(def_obj, slot)?;
        if !has_ctype_parent(field_desc, receiver, &mut seen)? {
            return Err(RuntimeError::Unimplemented {
                message: "ctype struct field must have CType as a parent",
            });
        }
        seen.clear();

        let decoded = decode_ctype_descriptor(
            vm,
            state,
            field_desc,
            &mut scratch,
            &mut decode_stack,
        )?;
        field_names.push(slot.name);
        field_values.push(field_desc);
        field_types.push(decoded.ffi_type);
    }

    let (struct_ffi_type, size, align, offsets) =
        compute_struct_layout(&field_types)?;
    let fields: Vec<CTypeField> = field_names
        .iter()
        .zip(field_values.iter())
        .zip(offsets.iter())
        .map(|((&name, &descriptor), &offset)| CTypeField {
            name,
            offset,
            descriptor,
        })
        .collect();

    let cache = CTypeCache {
        magic: CTYPE_CACHE_MAGIC,
        kind: CTypeKind::Struct,
        ffi_type: struct_ffi_type,
        size,
        align,
        fields: fields.clone(),
    };
    let cache_value = alloc_ctype_cache_value(vm, state, &mut scratch, cache)?;

    let parent_name = intern_symbol(vm, state, "parent*")?;
    let impl_name = intern_symbol(vm, state, "impl")?;
    let size_name = intern_symbol(vm, state, "size")?;
    let align_name = intern_symbol(vm, state, "align")?;
    let mut slots = Vec::with_capacity(field_names.len() + 4);
    slots.push(Slot::new(
        SlotFlags::ENUMERABLE
            .with(SlotFlags::CONSTANT)
            .with(SlotFlags::PARENT),
        parent_name,
        receiver,
    ));
    slots.push(Slot::new(
        SlotFlags::ENUMERABLE.with(SlotFlags::CONSTANT),
        impl_name,
        cache_value,
    ));
    slots.push(Slot::new(
        SlotFlags::ENUMERABLE.with(SlotFlags::CONSTANT),
        size_name,
        Value::from_i64(size as i64),
    ));
    slots.push(Slot::new(
        SlotFlags::ENUMERABLE.with(SlotFlags::CONSTANT),
        align_name,
        Value::from_i64(align as i64),
    ));
    for (i, name) in field_names.iter().enumerate() {
        slots.push(Slot::new(
            SlotFlags::ENUMERABLE.with(SlotFlags::CONSTANT),
            *name,
            field_values[i],
        ));
    }

    let map_map = vm.special.map_map;
    let none = vm.special.none;
    scratch.push(cache_value);
    scratch.extend(field_values.iter().copied());
    let struct_descriptor =
        with_roots(vm, state, &mut scratch, |proxy, roots| unsafe {
            let map = alloc_map(
                proxy,
                roots,
                map_map,
                none,
                MapFlags::NONE,
                &slots,
                0,
            )
            .value();
            alloc_slot_object(proxy, roots, map, &[]).value()
        });

    Ok(struct_descriptor)
}

pub fn ctype_field_info_at(
    vm: &mut VM,
    state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let field_name = args.get(0).copied().ok_or(RuntimeError::TypeError {
        expected: "field name",
        got: Value::from_i64(0),
    })?;
    let wanted_ptr = expect_string(field_name)?;
    let wanted = unsafe { (*wanted_ptr).as_str() };

    let mut scratch = vec![receiver, field_name];
    let mut decode_stack = Vec::new();
    let desc = decode_ctype_descriptor(
        vm,
        state,
        receiver,
        &mut scratch,
        &mut decode_stack,
    )?;
    if !matches!(desc.kind, CTypeKind::Struct) {
        return Err(RuntimeError::Unimplemented {
            message: "ctype field info only supported for struct descriptors",
        });
    }

    let field = desc
        .fields
        .iter()
        .find(|field| value_name_eq(field.name, wanted))
        .copied()
        .ok_or(RuntimeError::Unimplemented {
            message: "unknown ctype struct field",
        })?;

    let offset_name = intern_symbol(vm, state, "offset")?;
    let type_name = intern_symbol(vm, state, "type")?;
    let slots = [
        Slot::new(
            SlotFlags::ENUMERABLE.with(SlotFlags::CONSTANT),
            offset_name,
            Value::from_i64(field.offset as i64),
        ),
        Slot::new(
            SlotFlags::ENUMERABLE.with(SlotFlags::CONSTANT),
            type_name,
            field.descriptor,
        ),
    ];
    let map_map = vm.special.map_map;
    let none = vm.special.none;
    scratch.push(field.descriptor);
    let result = with_roots(vm, state, &mut scratch, |proxy, roots| unsafe {
        let map =
            alloc_map(proxy, roots, map_map, none, MapFlags::NONE, &slots, 0)
                .value();
        alloc_slot_object(proxy, roots, map, &[]).value()
    });
    Ok(result)
}

pub fn ctype_scalar_tag(
    vm: &mut VM,
    state: &mut InterpreterState,
    receiver: Value,
    _args: &[Value],
) -> Result<Value, RuntimeError> {
    let mut scratch = vec![receiver];
    let mut decode_stack = Vec::new();
    let desc = decode_ctype_descriptor(
        vm,
        state,
        receiver,
        &mut scratch,
        &mut decode_stack,
    )?;
    if let Some(tag) = desc.kind.scalar_tag() {
        Ok(Value::from_i64(tag))
    } else {
        Ok(vm.special.none)
    }
}

fn expect_slot_object_ptr(
    value: Value,
) -> Result<*mut SlotObject, RuntimeError> {
    if !value.is_ref() {
        return Err(RuntimeError::TypeError {
            expected: "slot object",
            got: value,
        });
    }
    let header: &object::Header = unsafe { value.as_ref() };
    if header.object_type() != ObjectType::Slots {
        return Err(RuntimeError::TypeError {
            expected: "slot object",
            got: value,
        });
    }
    Ok(value.ref_bits() as *mut SlotObject)
}

fn value_name_eq(name_value: Value, wanted: &str) -> bool {
    if let Ok(sym_ptr) = expect_symbol(name_value) {
        let name: &VMSymbol = unsafe { &*sym_ptr };
        return unsafe { name.as_str() == wanted };
    }
    if let Ok(str_ptr) = expect_string(name_value) {
        let name: &VMString = unsafe { &*str_ptr };
        return unsafe { name.as_str() == wanted };
    }
    false
}

fn value_is_method_object(value: Value) -> bool {
    if !value.is_ref() {
        return false;
    }
    let header: &object::Header = unsafe { value.as_ref() };
    if header.object_type() != ObjectType::Slots {
        return false;
    }
    let obj: &SlotObject = unsafe { value.as_ref() };
    let map: &object::Map = unsafe { obj.map.as_ref() };
    map.has_code()
}

fn marshal_arg(
    desc: &CTypeDescriptor,
    value: Value,
) -> Result<FfiArgValue, RuntimeError> {
    match desc.kind {
        CTypeKind::Void => Err(RuntimeError::Unimplemented {
            message: "void is not a valid parameter type",
        }),
        CTypeKind::I8 => {
            let n = value_to_i64(value)?;
            let v =
                i8::try_from(n).map_err(|_| RuntimeError::Unimplemented {
                    message: "value out of i8 range",
                })?;
            Ok(FfiArgValue::I8(v))
        }
        CTypeKind::U8 => {
            let n = value_to_u64(value)?;
            let v =
                u8::try_from(n).map_err(|_| RuntimeError::Unimplemented {
                    message: "value out of u8 range",
                })?;
            Ok(FfiArgValue::U8(v))
        }
        CTypeKind::I16 => {
            let n = value_to_i64(value)?;
            let v =
                i16::try_from(n).map_err(|_| RuntimeError::Unimplemented {
                    message: "value out of i16 range",
                })?;
            Ok(FfiArgValue::I16(v))
        }
        CTypeKind::U16 => {
            let n = value_to_u64(value)?;
            let v =
                u16::try_from(n).map_err(|_| RuntimeError::Unimplemented {
                    message: "value out of u16 range",
                })?;
            Ok(FfiArgValue::U16(v))
        }
        CTypeKind::I32 => {
            let n = value_to_i64(value)?;
            let v =
                i32::try_from(n).map_err(|_| RuntimeError::Unimplemented {
                    message: "value out of i32 range",
                })?;
            Ok(FfiArgValue::I32(v))
        }
        CTypeKind::U32 => {
            let n = value_to_u64(value)?;
            let v =
                u32::try_from(n).map_err(|_| RuntimeError::Unimplemented {
                    message: "value out of u32 range",
                })?;
            Ok(FfiArgValue::U32(v))
        }
        CTypeKind::I64 => Ok(FfiArgValue::I64(value_to_i64(value)?)),
        CTypeKind::U64 => Ok(FfiArgValue::U64(value_to_u64(value)?)),
        CTypeKind::F32 => {
            let v = if value.is_fixnum() {
                expect_fixnum(value)? as f32
            } else {
                unsafe { (*expect_float(value)?).value as f32 }
            };
            Ok(FfiArgValue::F32(v))
        }
        CTypeKind::F64 => {
            let v = if value.is_fixnum() {
                expect_fixnum(value)? as f64
            } else {
                unsafe { (*expect_float(value)?).value }
            };
            Ok(FfiArgValue::F64(v))
        }
        CTypeKind::Pointer => {
            let ptr = value_to_pointer_bits(value)? as usize;
            Ok(FfiArgValue::Pointer(ptr))
        }
        CTypeKind::Size => {
            let raw = value_to_u64(value)?;
            let size = usize::try_from(raw).map_err(|_| {
                RuntimeError::Unimplemented {
                    message: "value out of size_t range",
                }
            })?;
            Ok(FfiArgValue::Size(size))
        }
        CTypeKind::Struct => {
            if desc.size == 0 {
                return Err(RuntimeError::Unimplemented {
                    message: "zero-sized struct arguments are not supported",
                });
            }

            if !value.is_ref() {
                return Err(RuntimeError::TypeError {
                    expected: "ByteArray or Alien for struct argument",
                    got: value,
                });
            }

            let header: &object::Header = unsafe { value.as_ref() };
            match header.object_type() {
                ObjectType::ByteArray => {
                    let ba_ptr = expect_bytearray(value)?;
                    let len = unsafe { (*ba_ptr).len() } as usize;
                    if len < desc.size {
                        return Err(RuntimeError::Unimplemented {
                            message: "struct argument bytearray too small",
                        });
                    }
                    let src = unsafe {
                        (ba_ptr as *const ByteArray).add(1) as *const u8
                    };
                    let mut bytes = vec![0u8; desc.size];
                    unsafe {
                        std::ptr::copy_nonoverlapping(
                            src,
                            bytes.as_mut_ptr(),
                            desc.size,
                        )
                    };
                    Ok(FfiArgValue::Struct(bytes))
                }
                ObjectType::Alien => {
                    let alien_ptr = expect_alien(value)?;
                    let ptr = unsafe { (*alien_ptr).ptr as *const u8 };
                    if ptr.is_null() {
                        return Err(RuntimeError::Unimplemented {
                            message: "struct argument alien pointer is null",
                        });
                    }
                    let alien_size = unsafe { (*alien_ptr).size } as usize;
                    if alien_size != 0 && alien_size < desc.size {
                        return Err(RuntimeError::Unimplemented {
                            message: "struct argument alien too small",
                        });
                    }
                    let mut bytes = vec![0u8; desc.size];
                    unsafe {
                        std::ptr::copy_nonoverlapping(
                            ptr,
                            bytes.as_mut_ptr(),
                            desc.size,
                        )
                    };
                    Ok(FfiArgValue::Struct(bytes))
                }
                _ => Err(RuntimeError::TypeError {
                    expected: "ByteArray or Alien for struct argument",
                    got: value,
                }),
            }
        }
    }
}

pub fn alien_call_with_types(
    vm: &mut VM,
    state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let param_types_v =
        args.get(0).copied().ok_or(RuntimeError::TypeError {
            expected: "Array of CTypes",
            got: Value::from_i64(0),
        })?;
    let arg_values_v = args.get(1).copied().ok_or(RuntimeError::TypeError {
        expected: "Array of argument values",
        got: Value::from_i64(0),
    })?;
    let return_type_v =
        args.get(2).copied().ok_or(RuntimeError::TypeError {
            expected: "CType return value",
            got: Value::from_i64(0),
        })?;

    let (_, fn_ptr) = alien_ptr(receiver)?;
    if fn_ptr == 0 {
        return Err(RuntimeError::Unimplemented {
            message: "function pointer is null",
        });
    }

    let type_arr = expect_array(param_types_v)?;
    let value_arr = expect_array(arg_values_v)?;
    let types = unsafe { (*type_arr).elements() };
    let values = unsafe { (*value_arr).elements() };
    if types.len() != values.len() {
        return Err(RuntimeError::Unimplemented {
            message: "parameter types and argument values length mismatch",
        });
    }

    let mut param_descs = Vec::with_capacity(types.len());
    let mut decode_stack = Vec::new();
    let mut decode_roots =
        vec![receiver, param_types_v, arg_values_v, return_type_v];
    for &type_value in types {
        param_descs.push(decode_ctype_descriptor(
            vm,
            state,
            type_value,
            &mut decode_roots,
            &mut decode_stack,
        )?);
    }
    let return_desc = decode_ctype_descriptor(
        vm,
        state,
        return_type_v,
        &mut decode_roots,
        &mut decode_stack,
    )?;

    let cif_key = CifCacheKey {
        fn_ptr,
        param_types: types.iter().map(|v| v.raw()).collect(),
        return_type: return_type_v.raw(),
    };

    let mut arg_storage = Vec::with_capacity(values.len());
    for (idx, &arg_value) in values.iter().enumerate() {
        let marshaled = marshal_arg(&param_descs[idx], arg_value)?;
        arg_storage.push(marshaled);
    }

    let mut ffi_args = Vec::with_capacity(arg_storage.len());
    let mut raw_args = Vec::with_capacity(arg_storage.len());
    for stored in &arg_storage {
        let arg = match stored {
            FfiArgValue::I8(v) => {
                raw_args.push(v as *const _ as *mut libc::c_void);
                Arg::new(v)
            }
            FfiArgValue::U8(v) => {
                raw_args.push(v as *const _ as *mut libc::c_void);
                Arg::new(v)
            }
            FfiArgValue::I16(v) => {
                raw_args.push(v as *const _ as *mut libc::c_void);
                Arg::new(v)
            }
            FfiArgValue::U16(v) => {
                raw_args.push(v as *const _ as *mut libc::c_void);
                Arg::new(v)
            }
            FfiArgValue::I32(v) => {
                raw_args.push(v as *const _ as *mut libc::c_void);
                Arg::new(v)
            }
            FfiArgValue::U32(v) => {
                raw_args.push(v as *const _ as *mut libc::c_void);
                Arg::new(v)
            }
            FfiArgValue::I64(v) => {
                raw_args.push(v as *const _ as *mut libc::c_void);
                Arg::new(v)
            }
            FfiArgValue::U64(v) => {
                raw_args.push(v as *const _ as *mut libc::c_void);
                Arg::new(v)
            }
            FfiArgValue::F32(v) => {
                raw_args.push(v as *const _ as *mut libc::c_void);
                Arg::new(v)
            }
            FfiArgValue::F64(v) => {
                raw_args.push(v as *const _ as *mut libc::c_void);
                Arg::new(v)
            }
            FfiArgValue::Pointer(v) => {
                raw_args.push(v as *const _ as *mut libc::c_void);
                Arg::new(v)
            }
            FfiArgValue::Size(v) => {
                raw_args.push(v as *const _ as *mut libc::c_void);
                Arg::new(v)
            }
            FfiArgValue::Struct(bytes) => {
                raw_args.push(bytes.as_ptr() as *mut libc::c_void);
                Arg::new(&bytes[0])
            }
        };
        ffi_args.push(arg);
    }

    let code = CodePtr(fn_ptr as *mut libc::c_void);
    let mut scratch =
        vec![receiver, param_types_v, arg_values_v, return_type_v];
    let result = with_thread_local_cif(
        cif_key,
        || {
            Cif::new(
                param_descs.iter().map(|d| d.ffi_type.clone()),
                return_desc.ffi_type.clone(),
            )
        },
        |cif| match return_desc.kind {
            CTypeKind::Void => {
                unsafe { cif.call::<()>(code, &ffi_args) };
                vm.special.none
            }
            CTypeKind::I8 => {
                Value::from_i64(
                    unsafe { cif.call::<i8>(code, &ffi_args) } as i64
                )
            }
            CTypeKind::U8 => {
                Value::from_i64(
                    unsafe { cif.call::<u8>(code, &ffi_args) } as i64
                )
            }
            CTypeKind::I16 => {
                Value::from_i64(
                    unsafe { cif.call::<i16>(code, &ffi_args) } as i64
                )
            }
            CTypeKind::U16 => {
                Value::from_i64(
                    unsafe { cif.call::<u16>(code, &ffi_args) } as i64
                )
            }
            CTypeKind::I32 => {
                Value::from_i64(
                    unsafe { cif.call::<i32>(code, &ffi_args) } as i64
                )
            }
            CTypeKind::U32 => {
                Value::from_i64(
                    unsafe { cif.call::<u32>(code, &ffi_args) } as i64
                )
            }
            CTypeKind::I64 => output_i64(vm, state, &mut scratch, unsafe {
                cif.call::<i64>(code, &ffi_args)
            }),
            CTypeKind::U64 => output_u64(vm, state, &mut scratch, unsafe {
                cif.call::<u64>(code, &ffi_args)
            }),
            CTypeKind::F32 => {
                let val = unsafe { cif.call::<f32>(code, &ffi_args) } as f64;
                with_roots(vm, state, &mut scratch, |proxy, roots| unsafe {
                    alloc_float(proxy, roots, val).value()
                })
            }
            CTypeKind::F64 => {
                let val = unsafe { cif.call::<f64>(code, &ffi_args) };
                with_roots(vm, state, &mut scratch, |proxy, roots| unsafe {
                    alloc_float(proxy, roots, val).value()
                })
            }
            CTypeKind::Pointer => {
                let ptr_val =
                    unsafe { cif.call::<usize>(code, &ffi_args) } as u64;
                with_roots(vm, state, &mut scratch, |proxy, roots| unsafe {
                    alloc_alien(proxy, roots, ptr_val, 0).value()
                })
            }
            CTypeKind::Size => {
                let size = unsafe { cif.call::<usize>(code, &ffi_args) };
                output_u64(vm, state, &mut scratch, size as u64)
            }
            CTypeKind::Struct => {
                let mut ret_bytes = vec![0u8; return_desc.size];
                unsafe {
                    raw::ffi_call(
                        cif.as_raw_ptr(),
                        Some(*code.as_safe_fun()),
                        ret_bytes.as_mut_ptr() as *mut libc::c_void,
                        raw_args.as_mut_ptr(),
                    );
                }

                with_roots(vm, state, &mut scratch, |proxy, roots| unsafe {
                    alloc_byte_array(proxy, roots, &ret_bytes).value()
                })
            }
        },
    );

    Ok(result)
}

// ── Bulk copy ────────────────────────────────────────────────────────

/// Copy bytes from this Alien into a ByteArray.
/// Selector: `_AlienCopyTo:From:Length:` (args: dst_ba, src_offset, length)
pub fn alien_copy_to_bytearray(
    _vm: &mut VM,
    _state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let dst_v = args.get(0).copied().ok_or(RuntimeError::TypeError {
        expected: "ByteArray",
        got: Value::from_i64(0),
    })?;
    let src_off = get_offset(args, 1)?;
    let len_v = args.get(2).copied().ok_or(RuntimeError::TypeError {
        expected: "length",
        got: Value::from_i64(0),
    })?;
    let len = expect_fixnum(len_v)?;
    if src_off < 0 || len < 0 {
        return Err(RuntimeError::Unimplemented {
            message: "alien copy: offsets must be non-negative",
        });
    }

    let (_, src_addr) = alien_ptr(receiver)?;
    check_bounds(src_addr, src_off, len as usize)?;

    let dst_ptr = expect_bytearray(dst_v)? as *mut ByteArray;
    let dst_len = unsafe { (*dst_ptr).len() } as i64;
    if len > dst_len {
        return Err(RuntimeError::Unimplemented {
            message: "alien copy: length exceeds ByteArray size",
        });
    }

    if len > 0 {
        let src = unsafe { (src_addr as *const u8).add(src_off as usize) };
        let dst = unsafe { dst_ptr.add(1) as *mut u8 };
        unsafe { std::ptr::copy_nonoverlapping(src, dst, len as usize) };
    }
    Ok(dst_v)
}

/// Copy bytes from a ByteArray into this Alien.
/// Selector: `_AlienCopyFrom:Offset:Length:` (args: src_ba, src_offset, length)
pub fn alien_copy_from_bytearray(
    _vm: &mut VM,
    _state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let src_v = args.get(0).copied().ok_or(RuntimeError::TypeError {
        expected: "ByteArray",
        got: Value::from_i64(0),
    })?;
    let src_off = get_offset(args, 1)?;
    let len_v = args.get(2).copied().ok_or(RuntimeError::TypeError {
        expected: "length",
        got: Value::from_i64(0),
    })?;
    let len = expect_fixnum(len_v)?;
    if src_off < 0 || len < 0 {
        return Err(RuntimeError::Unimplemented {
            message: "alien copy: offsets must be non-negative",
        });
    }

    let src_ptr = expect_bytearray(src_v)? as *const ByteArray;
    let src_len = unsafe { (*src_ptr).len() } as i64;
    if src_off + len > src_len {
        return Err(RuntimeError::Unimplemented {
            message: "alien copy: source offset+length exceeds ByteArray size",
        });
    }

    let (_, dst_addr) = alien_ptr(receiver)?;
    check_bounds(dst_addr, 0, len as usize)?;

    if len > 0 {
        let src =
            unsafe { (src_ptr.add(1) as *const u8).add(src_off as usize) };
        let dst = dst_addr as *mut u8;
        unsafe { std::ptr::copy_nonoverlapping(src, dst, len as usize) };
    }
    Ok(receiver)
}

// ── Library loading ──────────────────────────────────────────────────

/// Open a shared library by path.
/// Selector: `_LibraryOpen:` (arg: path string)
/// Returns a new Alien whose ptr is the dlopen handle.
#[cfg(target_family = "unix")]
pub fn alien_library_open(
    vm: &mut VM,
    state: &mut InterpreterState,
    _receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let path_v = args.get(0).copied().ok_or(RuntimeError::TypeError {
        expected: "string path",
        got: Value::from_i64(0),
    })?;
    let str_ptr = expect_string(path_v)?;
    let bytes = unsafe { (*str_ptr).as_bytes() };
    let cstr =
        CString::new(bytes).map_err(|_| RuntimeError::Unimplemented {
            message: "library path contains null bytes",
        })?;

    let handle = unsafe {
        dlopen(cstr.as_ptr(), 0x00002 /* RTLD_NOW */)
    };
    if handle.is_null() {
        return Err(RuntimeError::Unimplemented {
            message: "dlopen failed",
        });
    }

    let mut scratch = vec![path_v];
    let alien = with_roots(vm, state, &mut scratch, |proxy, roots| unsafe {
        alloc_alien(proxy, roots, handle as u64, 0).value()
    });
    Ok(alien)
}

#[cfg(target_os = "windows")]
pub fn alien_library_open(
    vm: &mut VM,
    state: &mut InterpreterState,
    _receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let path_v = args.get(0).copied().ok_or(RuntimeError::TypeError {
        expected: "string path",
        got: Value::from_i64(0),
    })?;
    let str_ptr = expect_string(path_v)?;
    let bytes = unsafe { (*str_ptr).as_bytes() };
    let cstr =
        CString::new(bytes).map_err(|_| RuntimeError::Unimplemented {
            message: "library path contains null bytes",
        })?;

    let handle = unsafe { LoadLibraryA(cstr.as_ptr()) };
    if handle.is_null() {
        return Err(RuntimeError::Unimplemented {
            message: "LoadLibraryA failed",
        });
    }

    let mut scratch = vec![path_v];
    let alien = with_roots(vm, state, &mut scratch, |proxy, roots| unsafe {
        alloc_alien(proxy, roots, handle as u64, 0).value()
    });
    Ok(alien)
}

#[cfg(not(any(target_family = "unix", target_os = "windows")))]
pub fn alien_library_open(
    _vm: &mut VM,
    _state: &mut InterpreterState,
    _receiver: Value,
    _args: &[Value],
) -> Result<Value, RuntimeError> {
    Err(RuntimeError::Unimplemented {
        message: "library loading not supported on this platform",
    })
}

/// Look up a symbol in a library handle Alien.
/// Selector: `_LibrarySym:` (arg: symbol name string)
/// Returns a new Alien whose ptr is the function/data pointer.
#[cfg(target_family = "unix")]
pub fn alien_library_sym(
    vm: &mut VM,
    state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let (_, handle) = alien_ptr(receiver)?;
    if handle == 0 {
        return Err(RuntimeError::Unimplemented {
            message: "library handle is null",
        });
    }
    let name_v = args.get(0).copied().ok_or(RuntimeError::TypeError {
        expected: "string symbol name",
        got: Value::from_i64(0),
    })?;
    let str_ptr = expect_string(name_v)?;
    let bytes = unsafe { (*str_ptr).as_bytes() };
    let cstr =
        CString::new(bytes).map_err(|_| RuntimeError::Unimplemented {
            message: "symbol name contains null bytes",
        })?;

    let sym = unsafe { dlsym(handle as *mut u8, cstr.as_ptr()) };
    if sym.is_null() {
        return Err(RuntimeError::Unimplemented {
            message: "dlsym failed: symbol not found",
        });
    }

    let mut scratch = vec![receiver, name_v];
    let alien = with_roots(vm, state, &mut scratch, |proxy, roots| unsafe {
        alloc_alien(proxy, roots, sym as u64, 0).value()
    });
    Ok(alien)
}

#[cfg(target_os = "windows")]
pub fn alien_library_sym(
    vm: &mut VM,
    state: &mut InterpreterState,
    receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let (_, handle) = alien_ptr(receiver)?;
    if handle == 0 {
        return Err(RuntimeError::Unimplemented {
            message: "library handle is null",
        });
    }
    let name_v = args.get(0).copied().ok_or(RuntimeError::TypeError {
        expected: "string symbol name",
        got: Value::from_i64(0),
    })?;
    let str_ptr = expect_string(name_v)?;
    let bytes = unsafe { (*str_ptr).as_bytes() };
    let cstr =
        CString::new(bytes).map_err(|_| RuntimeError::Unimplemented {
            message: "symbol name contains null bytes",
        })?;

    let sym = unsafe { GetProcAddress(handle as *mut u8, cstr.as_ptr()) };
    if sym.is_null() {
        return Err(RuntimeError::Unimplemented {
            message: "GetProcAddress failed: symbol not found",
        });
    }

    let mut scratch = vec![receiver, name_v];
    let alien = with_roots(vm, state, &mut scratch, |proxy, roots| unsafe {
        alloc_alien(proxy, roots, sym as u64, 0).value()
    });
    Ok(alien)
}

#[cfg(not(any(target_family = "unix", target_os = "windows")))]
pub fn alien_library_sym(
    _vm: &mut VM,
    _state: &mut InterpreterState,
    _receiver: Value,
    _args: &[Value],
) -> Result<Value, RuntimeError> {
    Err(RuntimeError::Unimplemented {
        message: "library loading not supported on this platform",
    })
}

/// Close a library handle.
/// Selector: `_LibraryClose`
#[cfg(target_family = "unix")]
pub fn alien_library_close(
    _vm: &mut VM,
    _state: &mut InterpreterState,
    receiver: Value,
    _args: &[Value],
) -> Result<Value, RuntimeError> {
    let ptr = expect_alien(receiver)? as *mut Alien;
    let handle = unsafe { (*ptr).ptr };
    if handle != 0 {
        unsafe { dlclose(handle as *mut u8) };
        unsafe { (*ptr).ptr = 0 };
    }
    Ok(receiver)
}

#[cfg(target_os = "windows")]
pub fn alien_library_close(
    _vm: &mut VM,
    _state: &mut InterpreterState,
    receiver: Value,
    _args: &[Value],
) -> Result<Value, RuntimeError> {
    let ptr = expect_alien(receiver)? as *mut Alien;
    let handle = unsafe { (*ptr).ptr };
    if handle != 0 {
        unsafe { FreeLibrary(handle as *mut u8) };
        unsafe { (*ptr).ptr = 0 };
    }
    Ok(receiver)
}

#[cfg(not(any(target_family = "unix", target_os = "windows")))]
pub fn alien_library_close(
    _vm: &mut VM,
    _state: &mut InterpreterState,
    _receiver: Value,
    _args: &[Value],
) -> Result<Value, RuntimeError> {
    Err(RuntimeError::Unimplemented {
        message: "library loading not supported on this platform",
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicUsize, Ordering};

    #[test]
    fn cif_store_reuses_same_signature() {
        static BUILDS: AtomicUsize = AtomicUsize::new(0);
        let key = CifCacheKey {
            fn_ptr: 1,
            param_types: vec![11, 12],
            return_type: 13,
        };

        with_thread_local_cif(
            key.clone(),
            || {
                BUILDS.fetch_add(1, Ordering::Relaxed);
                Cif::new([Type::i64(), Type::i64()], Type::i64())
            },
            |_| (),
        );
        with_thread_local_cif(
            key,
            || {
                BUILDS.fetch_add(1, Ordering::Relaxed);
                Cif::new([Type::i64(), Type::i64()], Type::i64())
            },
            |_| (),
        );
        assert_eq!(BUILDS.load(Ordering::Relaxed), 1);
    }

    #[test]
    fn cif_store_is_safe_under_parallel_lookup() {
        static BUILDS: AtomicUsize = AtomicUsize::new(0);
        let key = CifCacheKey {
            fn_ptr: 2,
            param_types: vec![21],
            return_type: 22,
        };

        let mut workers = Vec::new();
        for _ in 0..8 {
            let key_t = key.clone();
            workers.push(std::thread::spawn(move || {
                with_thread_local_cif(
                    key_t.clone(),
                    || {
                        BUILDS.fetch_add(1, Ordering::Relaxed);
                        Cif::new([Type::i64()], Type::i64())
                    },
                    |_| (),
                );
                with_thread_local_cif(
                    key_t,
                    || {
                        BUILDS.fetch_add(1, Ordering::Relaxed);
                        Cif::new([Type::i64()], Type::i64())
                    },
                    |_| (),
                );
            }));
        }

        for worker in workers {
            worker.join().expect("worker should join");
        }
        assert_eq!(BUILDS.load(Ordering::Relaxed), 8);
    }
}
