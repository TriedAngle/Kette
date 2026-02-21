use std::collections::{HashMap, HashSet};
use std::fs::File;
use std::io::{self, BufReader, BufWriter, Read, Write};
use std::path::Path;
use std::ptr::NonNull;
use std::sync::{atomic::AtomicU64, atomic::Ordering, Arc, Mutex};

use heap::{
    map_memory_at, GcStatus, Heap, HeapSettings, LargeAllocation, NO_BLOCK,
};
use object::{SpecialObjects, Value};

use crate::primitives;
use crate::{
    trace_object, LockRecord, ModuleImport, ModuleState, SharedVMData, VMProxy,
    OBJECT_SIZE_FN, VM,
};

const IMAGE_MAGIC: &[u8; 8] = b"KETTEIMG";
const IMAGE_VERSION: u32 = 1;

pub fn save_image(vm: &mut VM, path: &Path) -> io::Result<()> {
    ensure_save_preconditions(vm)?;

    {
        let vm_ptr: *mut VM = vm;
        unsafe { (*vm_ptr).heap_proxy.force_major_gc(&mut *vm_ptr) };
    }

    ensure_save_preconditions(vm)?;

    let mut writer = BufWriter::new(File::create(path)?);

    writer.write_all(IMAGE_MAGIC)?;
    write_u32(&mut writer, IMAGE_VERSION)?;
    write_u64(&mut writer, primitive_hash(&vm.shared.primitives))?;

    write_heap_settings(&mut writer, &vm.heap_proxy.heap.settings)?;

    let heap = &vm.heap_proxy.heap;
    write_u64(&mut writer, heap.heap_start as usize as u64)?;
    write_u64(&mut writer, heap.settings.heap_size as u64)?;

    unsafe {
        let bytes = std::slice::from_raw_parts(
            heap.heap_start,
            heap.settings.heap_size,
        );
        writer.write_all(bytes)?;
    }

    write_u64(&mut writer, heap.info.block_count as u64)?;
    for block in heap.blocks.iter() {
        write_u8(&mut writer, block.status.load(Ordering::Relaxed))?;
        write_u64(&mut writer, block.next.load(Ordering::Relaxed) as u64)?;
        write_u8(
            &mut writer,
            if block.evac_candidate.load(Ordering::Relaxed) {
                1
            } else {
                0
            },
        )?;
        write_u16(&mut writer, block.prev_marked.load(Ordering::Relaxed))?;
    }

    write_u64(&mut writer, heap.info.line_count as u64)?;
    for line in heap.lines.iter() {
        write_u8(&mut writer, line.load(Ordering::Relaxed))?;
    }

    write_u64(
        &mut writer,
        heap.track.fresh_block_cursor.load(Ordering::Relaxed) as u64,
    )?;
    write_u8(&mut writer, heap.track.epoch.load(Ordering::Relaxed))?;
    write_u64(
        &mut writer,
        heap.track.minor_allocated.load(Ordering::Relaxed) as u64,
    )?;
    write_u64(
        &mut writer,
        heap.track.major_allocated.load(Ordering::Relaxed) as u64,
    )?;
    write_u32(
        &mut writer,
        heap.track.minor_since_major.load(Ordering::Relaxed),
    )?;
    write_u64(&mut writer, heap.available.load(Ordering::Relaxed) as u64)?;
    write_u64(&mut writer, heap.full_blocks.load(Ordering::Relaxed) as u64)?;

    let large = heap.large_objects.lock().expect("large_objects poisoned");
    write_u64(&mut writer, large.len() as u64)?;
    for alloc in large.iter() {
        let alloc_ref = unsafe { alloc.as_ref() };
        let base = alloc.as_ptr() as usize as u64;
        write_u64(&mut writer, base)?;
        write_u64(&mut writer, alloc_ref.size as u64)?;
        unsafe {
            let bytes = std::slice::from_raw_parts(
                alloc.as_ptr() as *const u8,
                alloc_ref.size,
            );
            writer.write_all(bytes)?;
        }
    }

    write_special_objects(&mut writer, vm.special)?;
    write_u64(&mut writer, vm.assoc_map.raw())?;
    write_u64(&mut writer, vm.dictionary.raw())?;
    write_opt_string(&mut writer, vm.current_module.as_deref())?;
    write_u64(
        &mut writer,
        vm.shared.next_thread_id.load(Ordering::Relaxed),
    )?;

    {
        let table = vm
            .shared
            .intern_table
            .lock()
            .expect("intern table poisoned");
        write_u64(&mut writer, table.len() as u64)?;
        for (name, value) in table.iter() {
            write_string(&mut writer, name)?;
            write_u64(&mut writer, value.raw())?;
        }
    }

    {
        let modules = vm.shared.modules.lock().expect("modules poisoned");
        write_u64(&mut writer, modules.len() as u64)?;
        for (path, module) in modules.iter() {
            write_string(&mut writer, path)?;
            write_module_state(&mut writer, module)?;
        }
    }

    writer.flush()?;
    Ok(())
}

pub fn load_image(path: &Path) -> io::Result<VMProxy> {
    let mut reader = BufReader::new(File::open(path)?);

    let mut magic = [0u8; 8];
    reader.read_exact(&mut magic)?;
    if &magic != IMAGE_MAGIC {
        return Err(invalid_data("invalid image magic"));
    }

    let version = read_u32(&mut reader)?;
    if version != IMAGE_VERSION {
        return Err(invalid_data("unsupported image version"));
    }

    let image_primitive_hash = read_u64(&mut reader)?;
    let runtime_primitives = primitives::default_primitives();
    let runtime_primitive_hash = primitive_hash(&runtime_primitives);
    if image_primitive_hash != runtime_primitive_hash {
        return Err(invalid_data("primitive ABI mismatch"));
    }

    let settings = read_heap_settings(&mut reader)?;
    let heap_base = read_u64(&mut reader)? as usize;
    let heap_size = read_u64(&mut reader)? as usize;
    if heap_size != settings.heap_size {
        return Err(invalid_data("heap size mismatch"));
    }

    let heap_ptr = NonNull::new(heap_base as *mut u8)
        .ok_or_else(|| invalid_data("invalid heap base pointer"))?;
    let mapped = map_memory_at(heap_ptr, heap_size)
        .ok_or_else(|| invalid_data("failed to map heap at saved address"))?;

    unsafe {
        let dst = std::slice::from_raw_parts_mut(mapped.as_ptr(), heap_size);
        reader.read_exact(dst)?;
    }

    let block_count = read_u64(&mut reader)? as usize;
    let mut block_meta = Vec::with_capacity(block_count);
    for _ in 0..block_count {
        block_meta.push((
            read_u8(&mut reader)?,
            read_u64(&mut reader)? as usize,
            read_u8(&mut reader)? != 0,
            read_u16(&mut reader)?,
        ));
    }

    let line_count = read_u64(&mut reader)? as usize;
    let mut lines = vec![0u8; line_count];
    reader.read_exact(&mut lines)?;

    let fresh_block_cursor = read_u64(&mut reader)? as usize;
    let epoch = read_u8(&mut reader)?;
    let minor_allocated = read_u64(&mut reader)? as usize;
    let major_allocated = read_u64(&mut reader)? as usize;
    let minor_since_major = read_u32(&mut reader)?;
    let available = read_u64(&mut reader)? as usize;
    let full_blocks = read_u64(&mut reader)? as usize;

    let large_count = read_u64(&mut reader)? as usize;
    let mut large_ptrs = Vec::with_capacity(large_count);
    for _ in 0..large_count {
        let base = read_u64(&mut reader)? as usize;
        let size = read_u64(&mut reader)? as usize;
        let base_ptr = NonNull::new(base as *mut u8)
            .ok_or_else(|| invalid_data("invalid large allocation base"))?;
        let mapped = map_memory_at(base_ptr, size).ok_or_else(|| {
            invalid_data("failed to map large allocation at saved address")
        })?;
        unsafe {
            let dst = std::slice::from_raw_parts_mut(mapped.as_ptr(), size);
            reader.read_exact(dst)?;
        }
        large_ptrs.push(mapped);
    }

    let special = read_special_objects(&mut reader)?;
    let assoc_map = Value::from_raw(read_u64(&mut reader)?);
    let dictionary = Value::from_raw(read_u64(&mut reader)?);
    let current_module = read_opt_string(&mut reader)?;
    let next_thread_id = read_u64(&mut reader)?;

    let intern_len = read_u64(&mut reader)? as usize;
    let mut intern_table = HashMap::with_capacity(intern_len);
    for _ in 0..intern_len {
        let key = read_string(&mut reader)?;
        let value = Value::from_raw(read_u64(&mut reader)?);
        intern_table.insert(key, value);
    }

    let modules_len = read_u64(&mut reader)? as usize;
    let mut modules = HashMap::with_capacity(modules_len);
    for _ in 0..modules_len {
        let path = read_string(&mut reader)?;
        let module = read_module_state(&mut reader)?;
        modules.insert(path, module);
    }

    let heap = Heap::from_mapped(
        settings,
        trace_object,
        OBJECT_SIZE_FN,
        mapped.as_ptr(),
    );

    if block_meta.len() != heap.blocks.len() {
        return Err(invalid_data("block metadata size mismatch"));
    }
    if lines.len() != heap.lines.len() {
        return Err(invalid_data("line metadata size mismatch"));
    }

    for (i, (status, next, evac, prev_marked)) in block_meta.iter().enumerate()
    {
        if *next != NO_BLOCK && *next >= heap.blocks.len() {
            return Err(invalid_data("invalid block next pointer in image"));
        }
        let block = &heap.blocks[i];
        block.status.store(*status, Ordering::Relaxed);
        block.next.store(*next, Ordering::Relaxed);
        block.evac_candidate.store(*evac, Ordering::Relaxed);
        block.prev_marked.store(*prev_marked, Ordering::Relaxed);
    }

    for (line, val) in heap.lines.iter().zip(lines.iter()) {
        line.store(*val, Ordering::Relaxed);
    }

    heap.track
        .fresh_block_cursor
        .store(fresh_block_cursor, Ordering::Relaxed);
    heap.track.epoch.store(epoch.max(1), Ordering::Relaxed);
    heap.track
        .minor_allocated
        .store(minor_allocated, Ordering::Relaxed);
    heap.track
        .major_allocated
        .store(major_allocated, Ordering::Relaxed);
    heap.track
        .minor_since_major
        .store(minor_since_major, Ordering::Relaxed);
    heap.available.store(available, Ordering::Relaxed);
    heap.full_blocks.store(full_blocks, Ordering::Relaxed);

    {
        let mut large =
            heap.large_objects.lock().expect("large_objects poisoned");
        for ptr in large_ptrs {
            let alloc_ptr = unsafe {
                NonNull::new_unchecked(ptr.as_ptr() as *mut LargeAllocation)
            };
            large.push(alloc_ptr);
        }
    }

    let shared = Arc::new(SharedVMData {
        heap: heap.clone(),
        special,
        primitives: runtime_primitives,
        assoc_map,
        dictionary,
        intern_table: Mutex::new(intern_table),
        modules: Mutex::new(modules),
        next_thread_id: AtomicU64::new(next_thread_id),
        platform_threads: Mutex::new(HashMap::new()),
        lock_records: Mutex::new(HashMap::<u64, Arc<LockRecord>>::new()),
    });

    let mut vm = VMProxy::new(shared);
    vm.current_module = current_module;
    Ok(vm)
}

fn ensure_save_preconditions(vm: &VM) -> io::Result<()> {
    let (status, _, threads, _) =
        vm.heap_proxy.heap.sync.state.load(Ordering::Acquire);
    if status != GcStatus::None {
        return Err(invalid_data("cannot save image while GC is active"));
    }
    if threads != 1 {
        return Err(invalid_data("image save requires exactly one VM thread"));
    }

    let threads = vm
        .shared
        .platform_threads
        .lock()
        .expect("platform threads poisoned");
    if !threads.is_empty() {
        return Err(invalid_data(
            "cannot save image with active platform threads",
        ));
    }

    Ok(())
}

fn primitive_hash(primitives: &[crate::primitives::PrimitiveDesc]) -> u64 {
    use std::hash::{Hash, Hasher};
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    for p in primitives {
        p.name.hash(&mut hasher);
        p.arity.hash(&mut hasher);
    }
    hasher.finish()
}

fn write_heap_settings(w: &mut dyn Write, s: &HeapSettings) -> io::Result<()> {
    write_u64(w, s.heap_size as u64)?;
    write_u64(w, s.block_size as u64)?;
    write_u64(w, s.line_size as u64)?;
    write_u64(w, s.large_size as u64)?;
    write_f64(w, s.bytes_before_gc)?;
    write_f64(w, s.nursery_fraction)?;
    write_f64(w, s.minor_recycle_threshold)?;
    write_u32(w, s.max_minor_before_major)?;
    Ok(())
}

fn read_heap_settings(r: &mut dyn Read) -> io::Result<HeapSettings> {
    Ok(HeapSettings {
        heap_size: read_u64(r)? as usize,
        block_size: read_u64(r)? as usize,
        line_size: read_u64(r)? as usize,
        large_size: read_u64(r)? as usize,
        bytes_before_gc: read_f64(r)?,
        nursery_fraction: read_f64(r)?,
        minor_recycle_threshold: read_f64(r)?,
        max_minor_before_major: read_u32(r)?,
    })
}

fn write_special_objects(
    w: &mut dyn Write,
    s: SpecialObjects,
) -> io::Result<()> {
    let values = [
        s.none,
        s.true_obj,
        s.false_obj,
        s.map_map,
        s.object,
        s.block_traits,
        s.array_traits,
        s.bytearray_traits,
        s.bignum_traits,
        s.alien_traits,
        s.string_traits,
        s.symbol_traits,
        s.ratio_traits,
        s.fixnum_traits,
        s.code_traits,
        s.float_traits,
        s.mirror,
    ];
    for value in values {
        write_u64(w, value.raw())?;
    }
    Ok(())
}

fn read_special_objects(r: &mut dyn Read) -> io::Result<SpecialObjects> {
    Ok(SpecialObjects {
        none: Value::from_raw(read_u64(r)?),
        true_obj: Value::from_raw(read_u64(r)?),
        false_obj: Value::from_raw(read_u64(r)?),
        map_map: Value::from_raw(read_u64(r)?),
        object: Value::from_raw(read_u64(r)?),
        block_traits: Value::from_raw(read_u64(r)?),
        array_traits: Value::from_raw(read_u64(r)?),
        bytearray_traits: Value::from_raw(read_u64(r)?),
        bignum_traits: Value::from_raw(read_u64(r)?),
        alien_traits: Value::from_raw(read_u64(r)?),
        string_traits: Value::from_raw(read_u64(r)?),
        symbol_traits: Value::from_raw(read_u64(r)?),
        ratio_traits: Value::from_raw(read_u64(r)?),
        fixnum_traits: Value::from_raw(read_u64(r)?),
        code_traits: Value::from_raw(read_u64(r)?),
        float_traits: Value::from_raw(read_u64(r)?),
        mirror: Value::from_raw(read_u64(r)?),
    })
}

fn write_module_state(
    w: &mut dyn Write,
    module: &ModuleState,
) -> io::Result<()> {
    write_u64(w, module.bindings.len() as u64)?;
    for (name, value) in &module.bindings {
        write_string(w, name)?;
        write_u64(w, value.raw())?;
    }

    write_u64(w, module.imports.len() as u64)?;
    for (name, import) in &module.imports {
        write_string(w, name)?;
        write_string(w, &import.module_path)?;
        write_string(w, &import.export_name)?;
    }

    write_u64(w, module.uses.len() as u64)?;
    for use_path in &module.uses {
        write_string(w, use_path)?;
    }

    write_u64(w, module.exports.len() as u64)?;
    for export in &module.exports {
        write_string(w, export)?;
    }

    Ok(())
}

fn read_module_state(r: &mut dyn Read) -> io::Result<ModuleState> {
    let bindings_len = read_u64(r)? as usize;
    let mut bindings = HashMap::with_capacity(bindings_len);
    for _ in 0..bindings_len {
        let name = read_string(r)?;
        let value = Value::from_raw(read_u64(r)?);
        bindings.insert(name, value);
    }

    let imports_len = read_u64(r)? as usize;
    let mut imports = HashMap::with_capacity(imports_len);
    for _ in 0..imports_len {
        let name = read_string(r)?;
        let module_path = read_string(r)?;
        let export_name = read_string(r)?;
        imports.insert(
            name,
            ModuleImport {
                module_path,
                export_name,
            },
        );
    }

    let uses_len = read_u64(r)? as usize;
    let mut uses = Vec::with_capacity(uses_len);
    for _ in 0..uses_len {
        uses.push(read_string(r)?);
    }

    let exports_len = read_u64(r)? as usize;
    let mut exports = HashSet::with_capacity(exports_len);
    for _ in 0..exports_len {
        exports.insert(read_string(r)?);
    }

    Ok(ModuleState {
        bindings,
        imports,
        uses,
        exports,
    })
}

fn write_u8(w: &mut dyn Write, v: u8) -> io::Result<()> {
    w.write_all(&[v])
}

fn read_u8(r: &mut dyn Read) -> io::Result<u8> {
    let mut b = [0u8; 1];
    r.read_exact(&mut b)?;
    Ok(b[0])
}

fn write_u16(w: &mut dyn Write, v: u16) -> io::Result<()> {
    w.write_all(&v.to_le_bytes())
}

fn read_u16(r: &mut dyn Read) -> io::Result<u16> {
    let mut b = [0u8; 2];
    r.read_exact(&mut b)?;
    Ok(u16::from_le_bytes(b))
}

fn write_u32(w: &mut dyn Write, v: u32) -> io::Result<()> {
    w.write_all(&v.to_le_bytes())
}

fn read_u32(r: &mut dyn Read) -> io::Result<u32> {
    let mut b = [0u8; 4];
    r.read_exact(&mut b)?;
    Ok(u32::from_le_bytes(b))
}

fn write_u64(w: &mut dyn Write, v: u64) -> io::Result<()> {
    w.write_all(&v.to_le_bytes())
}

fn read_u64(r: &mut dyn Read) -> io::Result<u64> {
    let mut b = [0u8; 8];
    r.read_exact(&mut b)?;
    Ok(u64::from_le_bytes(b))
}

fn write_f64(w: &mut dyn Write, v: f64) -> io::Result<()> {
    w.write_all(&v.to_le_bytes())
}

fn read_f64(r: &mut dyn Read) -> io::Result<f64> {
    let mut b = [0u8; 8];
    r.read_exact(&mut b)?;
    Ok(f64::from_le_bytes(b))
}

fn write_string(w: &mut dyn Write, s: &str) -> io::Result<()> {
    let bytes = s.as_bytes();
    write_u32(w, bytes.len() as u32)?;
    w.write_all(bytes)
}

fn read_string(r: &mut dyn Read) -> io::Result<String> {
    let len = read_u32(r)? as usize;
    let mut buf = vec![0u8; len];
    r.read_exact(&mut buf)?;
    String::from_utf8(buf).map_err(|_| invalid_data("invalid utf-8 in image"))
}

fn write_opt_string(w: &mut dyn Write, s: Option<&str>) -> io::Result<()> {
    match s {
        Some(value) => {
            write_u8(w, 1)?;
            write_string(w, value)
        }
        None => write_u8(w, 0),
    }
}

fn read_opt_string(r: &mut dyn Read) -> io::Result<Option<String>> {
    let tag = read_u8(r)?;
    match tag {
        0 => Ok(None),
        1 => Ok(Some(read_string(r)?)),
        _ => Err(invalid_data("invalid option tag in image")),
    }
}

fn invalid_data(msg: &str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, msg)
}

#[cfg(test)]
mod tests {
    use super::*;
    use parser::{Lexer, Parser};

    fn execute_source(vm: &mut VM, source: &str) -> Result<Value, String> {
        if vm.current_module.is_none() {
            vm.open_module(crate::USER_MODULE);
        }

        let parse_results: Vec<_> =
            Parser::new(Lexer::from_str(source)).collect();
        let parse_errors: Vec<String> = parse_results
            .iter()
            .filter_map(|r| r.as_ref().err())
            .map(|e| format!("Parse error: {e}"))
            .collect();
        if !parse_errors.is_empty() {
            return Err(parse_errors.join("\n"));
        }

        let exprs: Vec<parser::ast::Expr> =
            parse_results.into_iter().map(|r| r.unwrap()).collect();
        let code_desc = crate::compiler0::Compiler::compile_for_vm(vm, &exprs)
            .map_err(|e| format!("Compile error: {e}"))?;
        let code = crate::materialize::materialize(vm, &code_desc);
        crate::interpreter::interpret(vm, code)
            .map_err(|e| format!("Runtime error: {:?}", e.error))
    }

    fn default_core_files_for_test() -> Vec<std::path::PathBuf> {
        let core_dir =
            std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../core");
        let mut files: Vec<std::path::PathBuf> = std::fs::read_dir(core_dir)
            .expect("read core directory")
            .flatten()
            .map(|entry| entry.path())
            .filter(|path| path.is_file())
            .filter(|path| {
                path.extension().and_then(|ext| ext.to_str()) == Some("ktt")
            })
            .collect();

        files.sort_by_key(|path| {
            let name = path
                .file_name()
                .and_then(|name| name.to_str())
                .unwrap_or_default();
            let rank = match name {
                "init.ktt" => 0,
                "math.ktt" => 1,
                "collections.ktt" => 2,
                "alien.ktt" => 3,
                "system.ktt" => 4,
                "os.ktt" => 5,
                _ => 6,
            };
            (rank, name.to_string())
        });

        files
    }

    fn load_all_core_files(vm: &mut VM) {
        for file in default_core_files_for_test() {
            let source = std::fs::read_to_string(&file).unwrap_or_else(|e| {
                panic!("read {} failed: {e}", file.display())
            });
            execute_source(vm, &source).unwrap_or_else(|e| {
                panic!("execute {} failed: {e}", file.display())
            });
        }
    }

    fn temp_image_path() -> std::path::PathBuf {
        let mut path = std::env::temp_dir();
        let nanos = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .expect("clock before unix epoch")
            .as_nanos();
        path.push(format!(
            "kette-image-test-{}-{nanos}.img",
            std::process::id()
        ));
        path
    }

    #[test]
    fn core_alien_exports_include_ctype_before_system_load() {
        let mut vm = crate::special::bootstrap(HeapSettings::default());
        vm.open_module(crate::USER_MODULE);

        for file in default_core_files_for_test() {
            let name = file
                .file_name()
                .and_then(|n| n.to_str())
                .unwrap_or_default()
                .to_string();
            if name == "system.ktt" {
                break;
            }
            let source = std::fs::read_to_string(&file).unwrap_or_else(|e| {
                panic!("read {} failed: {e}", file.display())
            });
            execute_source(&mut vm, &source).unwrap_or_else(|e| {
                panic!("execute {} failed: {e}", file.display())
            });
        }

        vm.with_modules(|modules| {
            let alien =
                modules.get("Alien").expect("Alien module should exist");
            assert!(
                alien.bindings.contains_key("CType"),
                "Alien module should bind CType"
            );
            assert!(
                alien.exports.contains("CType"),
                "Alien module exports should include CType"
            );
        });
    }

    #[test]
    fn image_roundtrip_preserves_core_and_modules() {
        let mut vm = crate::special::bootstrap(HeapSettings::default());
        vm.open_module(crate::USER_MODULE);
        load_all_core_files(&mut vm);

        execute_source(
            &mut vm,
            "Module open: 'Image::State. SavedValue := 42. SavedValue.",
        )
        .expect("seed image module state");

        execute_source(
            &mut vm,
            "Module open: 'Image::BeforeSave. Module use: 'OS. Disposable.",
        )
        .expect("Disposable should resolve before save");

        let image_path = temp_image_path();
        save_image(&mut vm, &image_path).expect("save image");

        drop(vm);

        let mut restored = load_image(&image_path).expect("load image");

        let restored_value = execute_source(
            &mut restored,
            "Module open: 'Image::State. SavedValue.",
        )
        .expect("read saved value from restored image");
        assert!(restored_value.is_fixnum());
        assert_eq!(unsafe { restored_value.to_i64() }, 42);

        execute_source(
            &mut restored,
            "Module open: 'Image::AfterLoad. Module use: 'OS. Disposable.",
        )
        .expect("Disposable should resolve after load");

        let _ = std::fs::remove_file(image_path);
    }
}
