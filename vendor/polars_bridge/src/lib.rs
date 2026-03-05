use std::cell::RefCell;
use std::ffi::{c_char, c_void, CStr};
use std::sync::atomic::{AtomicBool, AtomicI32, AtomicI64, Ordering};

use polars::prelude::*;
use rayon::prelude::*;

const KP_OK: i32 = 0;
const KP_ERR_NULL: i32 = 1;
const KP_ERR_INVALID_UTF8: i32 = 2;
const KP_ERR_RUNTIME: i32 = 3;
const KP_ERR_CALLBACK: i32 = 4;

thread_local! {
    static LAST_ERROR: RefCell<Option<String>> = RefCell::new(None);
}

#[repr(C)]
pub struct KpString {
    pub ptr: *mut u8,
    pub len: i32,
}

#[repr(C)]
pub struct KpDataFrame {
    df: DataFrame,
}

pub type KpI64RowCallback = unsafe extern "C" fn(
    row_idx: i64,
    value: i64,
    user_data: *mut c_void,
) -> i32;

fn clear_last_error() {
    LAST_ERROR.with(|slot| {
        *slot.borrow_mut() = None;
    });
}

fn set_last_error(msg: impl Into<String>) {
    LAST_ERROR.with(|slot| {
        *slot.borrow_mut() = Some(msg.into());
    });
}

fn fail(msg: impl Into<String>, code: i32) -> i32 {
    set_last_error(msg);
    code
}

fn write_string_out(out: *mut KpString, value: String) -> i32 {
    if out.is_null() {
        return fail("output KpString pointer is null", KP_ERR_NULL);
    }

    let mut bytes = value.into_bytes().into_boxed_slice();
    let ptr = bytes.as_mut_ptr();
    let len = match i32::try_from(bytes.len()) {
        Ok(v) => v,
        Err(_) => return fail("string is too large to export", KP_ERR_RUNTIME),
    };
    std::mem::forget(bytes);

    unsafe {
        (*out).ptr = ptr;
        (*out).len = len;
    }
    KP_OK
}

unsafe fn cstr_arg(ptr: *const c_char, what: &str) -> Result<String, i32> {
    if ptr.is_null() {
        return Err(fail(format!("{what} pointer is null"), KP_ERR_NULL));
    }
    CStr::from_ptr(ptr)
        .to_str()
        .map(|s| s.to_owned())
        .map_err(|_| {
            fail(format!("{what} is not valid UTF-8"), KP_ERR_INVALID_UTF8)
        })
}

fn parse_csv_columns(input: &str) -> Vec<&str> {
    input
        .split(',')
        .map(str::trim)
        .filter(|s| !s.is_empty())
        .collect()
}

unsafe fn alloc_df_out(out_df: *mut *mut KpDataFrame, df: DataFrame) -> i32 {
    if out_df.is_null() {
        return fail("output dataframe pointer is null", KP_ERR_NULL);
    }
    let boxed = Box::new(KpDataFrame { df });
    *out_df = Box::into_raw(boxed);
    KP_OK
}

#[no_mangle]
pub extern "C" fn kp_version_major() -> i32 {
    0
}

#[no_mangle]
pub extern "C" fn kp_version_minor() -> i32 {
    1
}

#[no_mangle]
pub extern "C" fn kp_runtime_smoke_test() -> i32 {
    clear_last_error();
    KP_OK
}

#[no_mangle]
pub unsafe extern "C" fn kp_df_from_csv(
    path: *const c_char,
    out_df: *mut *mut KpDataFrame,
) -> i32 {
    let path = match cstr_arg(path, "path") {
        Ok(v) => v,
        Err(code) => return code,
    };

    let df = match CsvReadOptions::default()
        .with_has_header(true)
        .try_into_reader_with_file_path(Some(path.into()))
        .and_then(|reader| reader.finish())
    {
        Ok(df) => df,
        Err(err) => {
            return fail(format!("failed to read CSV: {err}"), KP_ERR_RUNTIME)
        }
    };

    let code = alloc_df_out(out_df, df);
    if code == KP_OK {
        clear_last_error();
    }
    code
}

#[no_mangle]
pub unsafe extern "C" fn kp_df_select_csv(
    df: *const KpDataFrame,
    columns_csv: *const c_char,
    out_df: *mut *mut KpDataFrame,
) -> i32 {
    if df.is_null() {
        return fail("input dataframe pointer is null", KP_ERR_NULL);
    }

    let columns_csv = match cstr_arg(columns_csv, "columns_csv") {
        Ok(v) => v,
        Err(code) => return code,
    };
    let columns = parse_csv_columns(&columns_csv);
    if columns.is_empty() {
        return fail("columns_csv is empty", KP_ERR_RUNTIME);
    }

    let out = match (*df).df.select(columns) {
        Ok(df) => df,
        Err(err) => {
            return fail(format!("select failed: {err}"), KP_ERR_RUNTIME)
        }
    };

    let code = alloc_df_out(out_df, out);
    if code == KP_OK {
        clear_last_error();
    }
    code
}

#[no_mangle]
pub unsafe extern "C" fn kp_df_filter_eq_i64(
    df: *const KpDataFrame,
    column: *const c_char,
    value: i64,
    out_df: *mut *mut KpDataFrame,
) -> i32 {
    if df.is_null() {
        return fail("input dataframe pointer is null", KP_ERR_NULL);
    }

    let column = match cstr_arg(column, "column") {
        Ok(v) => v,
        Err(code) => return code,
    };

    let out = match (*df)
        .df
        .clone()
        .lazy()
        .filter(col(&column).eq(lit(value)))
        .collect()
    {
        Ok(df) => df,
        Err(err) => {
            return fail(format!("filter failed: {err}"), KP_ERR_RUNTIME)
        }
    };

    let code = alloc_df_out(out_df, out);
    if code == KP_OK {
        clear_last_error();
    }
    code
}

#[no_mangle]
pub unsafe extern "C" fn kp_df_groupby_sum(
    df: *const KpDataFrame,
    key_col: *const c_char,
    value_col: *const c_char,
    out_df: *mut *mut KpDataFrame,
) -> i32 {
    if df.is_null() {
        return fail("input dataframe pointer is null", KP_ERR_NULL);
    }

    let key_col = match cstr_arg(key_col, "key_col") {
        Ok(v) => v,
        Err(code) => return code,
    };
    let value_col = match cstr_arg(value_col, "value_col") {
        Ok(v) => v,
        Err(code) => return code,
    };

    let out = match (*df)
        .df
        .clone()
        .lazy()
        .group_by([col(&key_col)])
        .agg([col(&value_col).sum().alias(&format!("{value_col}_sum"))])
        .collect()
    {
        Ok(df) => df,
        Err(err) => {
            return fail(format!("groupby sum failed: {err}"), KP_ERR_RUNTIME)
        }
    };

    let code = alloc_df_out(out_df, out);
    if code == KP_OK {
        clear_last_error();
    }
    code
}

#[no_mangle]
pub unsafe extern "C" fn kp_df_head(
    df: *const KpDataFrame,
    n: usize,
    out_df: *mut *mut KpDataFrame,
) -> i32 {
    if df.is_null() {
        return fail("input dataframe pointer is null", KP_ERR_NULL);
    }

    let out = (*df).df.head(Some(n));
    let code = alloc_df_out(out_df, out);
    if code == KP_OK {
        clear_last_error();
    }
    code
}

#[no_mangle]
pub unsafe extern "C" fn kp_df_to_pretty_string(
    df: *const KpDataFrame,
    out: *mut KpString,
) -> i32 {
    if df.is_null() {
        return fail("input dataframe pointer is null", KP_ERR_NULL);
    }

    let text = format!("{}", (*df).df);
    let code = write_string_out(out, text);
    if code == KP_OK {
        clear_last_error();
    }
    code
}

#[no_mangle]
pub unsafe extern "C" fn kp_df_for_each_i64(
    df: *const KpDataFrame,
    column: *const c_char,
    callback: Option<KpI64RowCallback>,
    user_data: *mut c_void,
    out_rows_visited: *mut i64,
) -> i32 {
    if df.is_null() {
        return fail("input dataframe pointer is null", KP_ERR_NULL);
    }
    if out_rows_visited.is_null() {
        return fail("output rows_visited pointer is null", KP_ERR_NULL);
    }

    let callback = match callback {
        Some(cb) => cb,
        None => return fail("callback pointer is null", KP_ERR_NULL),
    };

    let column = match cstr_arg(column, "column") {
        Ok(v) => v,
        Err(code) => return code,
    };

    let s = match (*df).df.column(&column) {
        Ok(series) => series,
        Err(err) => {
            return fail(format!("column lookup failed: {err}"), KP_ERR_RUNTIME)
        }
    };

    let values = match s.i64() {
        Ok(chunked) => chunked,
        Err(err) => {
            return fail(
                format!("column '{column}' is not i64: {err}"),
                KP_ERR_RUNTIME,
            )
        }
    };

    let mut indexed_values = Vec::new();
    for (idx, maybe_value) in values.into_iter().enumerate() {
        let Some(value) = maybe_value else {
            continue;
        };
        let row_idx = match i64::try_from(idx) {
            Ok(v) => v,
            Err(_) => {
                return fail(
                    "row index overflow during callback",
                    KP_ERR_RUNTIME,
                )
            }
        };
        indexed_values.push((row_idx, value));
    }

    let visited = AtomicI64::new(0);
    let stop_requested = AtomicBool::new(false);
    let callback_error_code = AtomicI32::new(0);
    let user_data_bits = user_data as usize;

    indexed_values.par_iter().for_each(|(row_idx, value)| {
        if stop_requested.load(Ordering::Relaxed)
            || callback_error_code.load(Ordering::Relaxed) != 0
        {
            return;
        }

        let user_data = user_data_bits as *mut c_void;
        let callback_code = unsafe { callback(*row_idx, *value, user_data) };
        visited.fetch_add(1, Ordering::Relaxed);

        if callback_code == 0 {
            return;
        }
        if callback_code == 1 {
            stop_requested.store(true, Ordering::Relaxed);
            return;
        }

        if callback_error_code
            .compare_exchange(
                0,
                callback_code,
                Ordering::Relaxed,
                Ordering::Relaxed,
            )
            .is_ok()
        {
            stop_requested.store(true, Ordering::Relaxed);
        }
    });

    let visited = visited.load(Ordering::Relaxed);
    *out_rows_visited = visited;

    let callback_error_code = callback_error_code.load(Ordering::Relaxed);
    if callback_error_code != 0 {
        return fail(
            format!("callback returned error code {callback_error_code}"),
            KP_ERR_CALLBACK,
        );
    }

    clear_last_error();
    KP_OK
}

#[no_mangle]
pub unsafe extern "C" fn kp_last_error_message(out: *mut KpString) -> i32 {
    let message =
        LAST_ERROR.with(|slot| slot.borrow().clone().unwrap_or_default());
    write_string_out(out, message)
}

#[no_mangle]
pub unsafe extern "C" fn kp_string_free(ptr: *mut u8, len: i32) {
    if ptr.is_null() {
        return;
    }
    let len = if len < 0 { 0 } else { len as usize };
    let raw = std::ptr::slice_from_raw_parts_mut(ptr, len);
    drop(Box::from_raw(raw));
}

#[no_mangle]
pub unsafe extern "C" fn kp_df_free(df: *mut KpDataFrame) {
    if df.is_null() {
        return;
    }
    drop(Box::from_raw(df));
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicI64, Ordering};

    #[repr(C)]
    struct RowState {
        sum: AtomicI64,
        valid_rows: AtomicI64,
        stop_after_valid: i64,
    }

    unsafe extern "C" fn collect_i64_rows(
        _row_idx: i64,
        value: i64,
        user_data: *mut c_void,
    ) -> i32 {
        let state = &mut *(user_data as *mut RowState);
        state.sum.fetch_add(value, Ordering::Relaxed);
        let seen = state.valid_rows.fetch_add(1, Ordering::Relaxed) + 1;
        if state.stop_after_valid >= 0 && seen >= state.stop_after_valid {
            return 1;
        }
        0
    }

    #[test]
    fn for_each_i64_callback_collects_and_can_stop() {
        let df = df!("amount" => &[Some(10_i64), None, Some(20), Some(7)])
            .expect("dataframe creation");
        let raw_df = Box::into_raw(Box::new(KpDataFrame { df }));

        let mut state = RowState {
            sum: AtomicI64::new(0),
            valid_rows: AtomicI64::new(0),
            stop_after_valid: 2,
        };
        let mut visited = -1_i64;
        let column = std::ffi::CString::new("amount").expect("cstring");

        let code = unsafe {
            kp_df_for_each_i64(
                raw_df,
                column.as_ptr(),
                Some(collect_i64_rows),
                (&mut state as *mut RowState).cast::<c_void>(),
                &mut visited,
            )
        };

        assert_eq!(code, KP_OK);
        let valid_rows = state.valid_rows.load(Ordering::Relaxed);
        let sum = state.sum.load(Ordering::Relaxed);
        assert!(valid_rows >= 2);
        assert!(valid_rows <= 3);
        assert!(sum >= 30);
        assert!(sum <= 37);
        assert_eq!(visited, valid_rows);

        unsafe { kp_df_free(raw_df) };
    }
}
