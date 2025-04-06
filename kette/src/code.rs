use std::{collections::HashMap, ptr::NonNull};

use crate::{
    Array, ByteArray, Context, LinkedListAllocator, Node, Object, Quotation,
    StackFn, Tagged, Word,
};

#[derive(Debug, Clone, Copy)]
pub enum Code {
    Push(Tagged), // any object
    CallQuotation,
    Call(Word),
    SendWord(*const ByteArray),
    CallPrimitive(StackFn),
    Branch,
    // TODO: Remove and actually inline this
    BranchInline(*const Quotation, *const Quotation),
}

pub struct CodeHeap {
    allocator: LinkedListAllocator,
    artifacts: HashMap<*const Quotation, NonNull<Node>>,
}

impl Context {
    fn compile(
        &self,
        heap: &mut CodeHeap,
        quot: *const Quotation,
    ) -> NonNull<Node> {
        if let Some(node_ptr) = heap.artifacts.get(&quot) {
            return *node_ptr;
        }

        let body = unsafe { (*quot).body }.to_ptr() as *const Array;
        let body_len = unsafe { (*body).len() };

        let mut code = Vec::new();
        let mut i = 0;

        while i < body_len {
            let item = unsafe { (*body).get(i) };

            if item.is_int() || item == Tagged::null() {
                code.push(Code::Push(item));
                i += 1;
                continue;
            }

            let obj_ptr = item.to_ptr();
            let map_ptr = unsafe { (*obj_ptr).header.get_map() };
            let map_tagged = Tagged::from_ptr(map_ptr as *mut Object);

            // Check for if-pattern: quotation, quotation
            if i + 2 < body_len && map_tagged == self.gc.specials.quotation_map
            {
                let next = unsafe { (*body).get(i + 1) };
                let next_next = unsafe { (*body).get(i + 2) };

                if self.is_quotation(next) && self.is_word(next_next) {
                    if let Some(fun) = self.word_primitive(next_next) {
                        if fun == crate::primitives::iff {
                            let true_branch = item.to_ptr() as *const Quotation;
                            let false_branch =
                                next.to_ptr() as *const Quotation;

                            self.compile(heap, true_branch);
                            self.compile(heap, false_branch);

                            code.push(Code::BranchInline(
                                true_branch,
                                false_branch,
                            ));
                            i += 3;
                            continue;
                        }
                    }
                }
            }

            if map_tagged == self.gc.specials.quotation_map {
                let quotation_ptr = obj_ptr as *const Quotation;
                self.compile(heap, quotation_ptr);
                code.push(Code::Push(item));
            } else if map_tagged == self.gc.specials.word_map {
                if let Some(primitive) = self.word_primitive(item) {
                    code.push(Code::CallPrimitive(primitive));
                } else {
                    let word_ptr = obj_ptr as *const Word;
                    code.push(Code::Call(unsafe {
                        *(word_ptr as *const Word)
                    }));
                }
            } else {
                code.push(Code::Push(item));
            }

            i += 1;
        }

        let node = heap.write_slice(&code);
        heap.map_artifact(quot, node);

        node
    }
}

impl CodeHeap {
    pub fn new() -> Self {
        CodeHeap {
            allocator: LinkedListAllocator::new(),
            artifacts: HashMap::new(),
        }
    }

    pub fn write_slice(&mut self, code: &[Code]) -> NonNull<Node> {
        let bytes = unsafe {
            std::slice::from_raw_parts(
                code.as_ptr() as *const u8,
                code.len() * std::mem::size_of::<Code>(),
            )
        };

        let allocated_bytes = self.allocator.allocate(bytes);
        allocated_bytes
    }

    pub fn map_artifact(
        &mut self,
        quotation: *const Quotation,
        node: NonNull<Node>,
    ) {
        self.artifacts.insert(quotation, node);
    }

    pub fn get_code_for_quotation(
        &self,
        quotation: *const Quotation,
    ) -> Option<&[Code]> {
        self.artifacts.get(&quotation).map(|&node_ptr| {
            let node = unsafe { node_ptr.as_ref() };
            let data_size = node.data_size;
            let len = data_size / std::mem::size_of::<Code>();
            let data_ptr = node.data_ptr() as *const Code;

            unsafe { std::slice::from_raw_parts(data_ptr, len) }
        })
    }
}

#[cfg(test)]
mod test {
    use crate::Context;
    use crate::ContextConfig;
    use crate::DEFAULT_BLOCK_SIZE;
    use crate::primitives;

    use super::*;

    #[derive(Debug, Clone, Copy, Default)]
    struct MockWord;

    #[derive(Debug, Clone, Copy, Default)]
    struct MockTagged;

    #[derive(Debug, Clone, Copy)]
    struct MockQuotation;

    fn mock_primitive(_ctx: &mut Context) {}
    impl Word {
        fn default() -> Self {
            unsafe { std::mem::zeroed() }
        }
    }

    impl Tagged {
        fn default() -> Self {
            unsafe { std::mem::zeroed() }
        }
    }
    #[test]
    fn test_linkedlist_heap_basic() {
        let mut code_heap = CodeHeap::new();

        let code1 = [
            Code::Push(Tagged::default()),
            Code::CallQuotation,
            Code::Call(Word::default()),
        ];

        let code2 = [Code::Branch, Code::CallPrimitive(mock_primitive)];

        let allocated_node1 = code_heap.write_slice(&code1);
        let allocated_node2 = code_heap.write_slice(&code2);

        let allocated_code1 =
            unsafe { allocated_node1.as_ref().data_as::<Code>() };
        let allocated_code2 =
            unsafe { allocated_node2.as_ref().data_as::<Code>() };

        assert_eq!(allocated_code1.len(), code1.len());
        assert_eq!(allocated_code2.len(), code2.len());

        for (i, code) in code1.iter().enumerate() {
            assert_eq!(
                std::mem::discriminant(code),
                std::mem::discriminant(&allocated_code1[i])
            );
        }

        for (i, code) in code2.iter().enumerate() {
            assert_eq!(
                std::mem::discriminant(code),
                std::mem::discriminant(&allocated_code2[i])
            );
        }
    }

    #[test]
    fn test_linkedlist_heap_quotation_mapping() {
        let mut code_heap = CodeHeap::new();

        let code1 = [
            Code::Push(Tagged::default()),
            Code::CallQuotation,
            Code::Call(Word::default()),
        ];

        let code2 = [Code::Branch, Code::CallPrimitive(mock_primitive)];

        let allocated_code1 = code_heap.write_slice(&code1);
        let allocated_code2 = code_heap.write_slice(&code2);

        let quotation1: *const Quotation = std::ptr::null();
        let quotation2 = unsafe {
            &*std::ptr::addr_of!(quotation1) as *const _ as *const Quotation
        };

        code_heap.map_artifact(quotation1, allocated_code1);
        code_heap.map_artifact(quotation2, allocated_code2);

        let retrieved_code1 =
            code_heap.get_code_for_quotation(quotation1).unwrap();
        let retrieved_code2 =
            code_heap.get_code_for_quotation(quotation2).unwrap();

        assert_eq!(retrieved_code1.len(), code1.len());
        assert_eq!(retrieved_code2.len(), code2.len());

        for (i, code) in code1.iter().enumerate() {
            assert_eq!(
                std::mem::discriminant(code),
                std::mem::discriminant(&retrieved_code1[i])
            );
        }

        for (i, code) in code2.iter().enumerate() {
            assert_eq!(
                std::mem::discriminant(code),
                std::mem::discriminant(&retrieved_code2[i])
            );
        }

        let quotation3: *const Quotation = std::ptr::null();

        let non_existent = unsafe {
            &*std::ptr::addr_of!(quotation3) as *const _ as *const Quotation
        };
        assert!(code_heap.get_code_for_quotation(non_existent).is_none());
    }

    #[test]
    fn test_linkedlist_heap_large_code() {
        let mut code_heap = CodeHeap::new();

        let node_size = std::mem::size_of::<Node>();
        let code_size = std::mem::size_of::<Code>();
        let max_codes = (DEFAULT_BLOCK_SIZE - node_size) / code_size;

        let large_code_size = max_codes + 100;
        let mut large_code = Vec::with_capacity(large_code_size);

        for _ in 0..large_code_size {
            large_code.push(Code::CallQuotation);
        }

        let allocated_large_node = code_heap.write_slice(&large_code);
        let allocated_large_code =
            unsafe { allocated_large_node.as_ref().data_as::<Code>() };

        assert_eq!(allocated_large_code.len(), large_code.len());

        let quotation = std::ptr::null();
        code_heap.map_artifact(quotation, allocated_large_node);

        let retrieved_code =
            code_heap.get_code_for_quotation(quotation).unwrap();
        assert_eq!(retrieved_code.len(), large_code.len());

        assert_eq!(
            std::mem::discriminant(&retrieved_code[0]),
            std::mem::discriminant(&Code::CallQuotation)
        );
        assert_eq!(
            std::mem::discriminant(&retrieved_code[large_code_size - 1]),
            std::mem::discriminant(&Code::CallQuotation)
        );
    }

    #[test]
    fn test_linkedlist_heap_multiple_allocations() {
        let mut code_heap = CodeHeap::new();
        let num_allocations = 50;

        let mut codes = Vec::with_capacity(num_allocations);
        let mut quotations = Vec::with_capacity(num_allocations);
        let mut allocated_codes = Vec::with_capacity(num_allocations);

        for i in 0..num_allocations {
            let mut code = Vec::with_capacity(10);
            for _ in 0..10 {
                code.push(if i % 2 == 0 {
                    Code::CallQuotation
                } else {
                    Code::Branch
                });
            }
            codes.push(code);

            let quotation = i as *const Quotation;
            quotations.push(quotation);
        }

        for code in &codes {
            allocated_codes.push(code_heap.write_slice(code));
        }

        for (i, &quotation) in quotations.iter().enumerate() {
            code_heap.map_artifact(quotation, allocated_codes[i]);
        }

        for (i, &quotation) in quotations.iter().enumerate() {
            let retrieved_code =
                code_heap.get_code_for_quotation(quotation).unwrap();
            assert_eq!(retrieved_code.len(), codes[i].len());

            for j in 0..retrieved_code.len() {
                assert_eq!(
                    std::mem::discriminant(&retrieved_code[j]),
                    std::mem::discriminant(&codes[i][j])
                );
            }
        }
    }

    fn setup_context() -> Context {
        let config = ContextConfig {
            data_size: 100,
            retian_size: 100,
            name_size: 100,
        };
        Context::new(&config)
    }

    #[test]
    fn test_compile_simple_quotation() {
        let mut ctx = setup_context();
        let mut code_heap = CodeHeap::new();

        let quotation_array = ctx.gc.allocate_array(1);
        unsafe {
            let array_ptr = quotation_array.to_ptr() as *mut Array;
            (*array_ptr).set(0, Tagged::from_int(42));
        }

        let quotation = ctx.gc.allocate_object(ctx.gc.specials.quotation_map);
        unsafe {
            let quotation_ptr = quotation.to_ptr();
            (*quotation_ptr).set_slot(0, Tagged::null());
            (*quotation_ptr).set_slot(1, quotation_array);
        }

        let node =
            ctx.compile(&mut code_heap, quotation.to_ptr() as *const Quotation);

        let code = code_heap
            .get_code_for_quotation(quotation.to_ptr() as *const Quotation)
            .unwrap();

        assert_eq!(code.len(), 1);
        match code[0] {
            Code::Push(value) => assert_eq!(value.to_int(), 42),
            _ => panic!("Expected Push operation"),
        }
    }

    #[test]
    fn test_compile_multi_item_quotation() {
        let mut ctx = setup_context();
        let mut code_heap = CodeHeap::new();

        let quotation_array = ctx.gc.allocate_array(3);
        unsafe {
            let array_ptr = quotation_array.to_ptr() as *mut Array;
            (*array_ptr).set(0, Tagged::from_int(1));
            (*array_ptr).set(1, Tagged::from_int(2));
            (*array_ptr).set(2, Tagged::from_int(3));
        }

        let quotation = ctx.gc.allocate_object(ctx.gc.specials.quotation_map);
        unsafe {
            let quotation_ptr = quotation.to_ptr();
            (*quotation_ptr).set_slot(0, Tagged::null());
            (*quotation_ptr).set_slot(1, quotation_array);
        }

        ctx.compile(&mut code_heap, quotation.to_ptr() as *const Quotation);

        let code = code_heap
            .get_code_for_quotation(quotation.to_ptr() as *const Quotation)
            .unwrap();

        assert_eq!(code.len(), 3);
        match code[0] {
            Code::Push(value) => assert_eq!(value.to_int(), 1),
            _ => panic!("Expected Push operation for first item"),
        }
        match code[1] {
            Code::Push(value) => assert_eq!(value.to_int(), 2),
            _ => panic!("Expected Push operation for second item"),
        }
        match code[2] {
            Code::Push(value) => assert_eq!(value.to_int(), 3),
            _ => panic!("Expected Push operation for third item"),
        }
    }

    #[test]
    fn test_compile_nested_quotation() {
        let mut ctx = setup_context();
        let mut code_heap = CodeHeap::new();

        let inner_array = ctx.gc.allocate_array(1);
        unsafe {
            let array_ptr = inner_array.to_ptr() as *mut Array;
            (*array_ptr).set(0, Tagged::from_int(42));
        }

        let inner_quotation =
            ctx.gc.allocate_object(ctx.gc.specials.quotation_map);
        unsafe {
            let quotation_ptr = inner_quotation.to_ptr();
            (*quotation_ptr).set_slot(0, Tagged::null());
            (*quotation_ptr).set_slot(1, inner_array);
        }

        let outer_array = ctx.gc.allocate_array(1);
        unsafe {
            let array_ptr = outer_array.to_ptr() as *mut Array;
            (*array_ptr).set(0, inner_quotation);
        }

        let outer_quotation =
            ctx.gc.allocate_object(ctx.gc.specials.quotation_map);
        unsafe {
            let quotation_ptr = outer_quotation.to_ptr();
            (*quotation_ptr).set_slot(0, Tagged::null());
            (*quotation_ptr).set_slot(1, outer_array);
        }

        ctx.compile(
            &mut code_heap,
            outer_quotation.to_ptr() as *const Quotation,
        );

        let outer_code =
            code_heap
                .get_code_for_quotation(
                    outer_quotation.to_ptr() as *const Quotation
                )
                .unwrap();
        let inner_code =
            code_heap
                .get_code_for_quotation(
                    inner_quotation.to_ptr() as *const Quotation
                )
                .unwrap();

        assert_eq!(outer_code.len(), 1);
        match outer_code[0] {
            Code::Push(value) => {
                assert_eq!(value.to_ptr(), inner_quotation.to_ptr())
            }
            _ => panic!("Expected Push operation for inner quotation"),
        }

        assert_eq!(inner_code.len(), 1);
        match inner_code[0] {
            Code::Push(value) => assert_eq!(value.to_int(), 42),
            _ => panic!("Expected Push operation for 42"),
        }
    }

    #[test]
    fn test_compile_word_call() {
        let mut ctx = setup_context();
        let mut code_heap = CodeHeap::new();

        let word_name = ctx.gc.allocate_string("test_word");
        let word = ctx.gc.allocate_object(ctx.gc.specials.word_map);
        unsafe {
            let word_ptr = word.to_ptr();
            (*word_ptr).set_slot(0, word_name);
            (*word_ptr).set_slot(1, Tagged::null());
            (*word_ptr).set_slot(2, Tagged::null());
        }

        let quotation_array = ctx.gc.allocate_array(1);
        unsafe {
            let array_ptr = quotation_array.to_ptr() as *mut Array;
            (*array_ptr).set(0, word);
        }

        let quotation = ctx.gc.allocate_object(ctx.gc.specials.quotation_map);
        unsafe {
            let quotation_ptr = quotation.to_ptr();
            (*quotation_ptr).set_slot(0, Tagged::null());
            (*quotation_ptr).set_slot(1, quotation_array);
        }

        ctx.compile(&mut code_heap, quotation.to_ptr() as *const Quotation);

        let code = code_heap
            .get_code_for_quotation(quotation.to_ptr() as *const Quotation)
            .unwrap();

        assert_eq!(code.len(), 1);
        match code[0] {
            Code::Call(ref w) => unsafe {
                let name_ptr = w.name.to_ptr() as *const ByteArray;
                assert_eq!((*name_ptr).as_str(), "test_word");
            },
            _ => panic!("Expected Call operation"),
        }
    }

    #[test]
    fn test_compile_primitive_word_call() {
        let mut ctx = setup_context();
        let mut code_heap = CodeHeap::new();

        let word_name = ctx.gc.allocate_string("primitive_word");
        let word = ctx.gc.allocate_object(ctx.gc.specials.word_map);
        let tags = ctx.gc.allocate_array(1);

        unsafe {
            let tags_ptr = tags.to_ptr() as *mut Array;
            (*tags_ptr).set(0, ctx.gc.specials.primitive_tag);

            let word_ptr = word.to_ptr();
            (*word_ptr).set_slot(0, word_name);
            (*word_ptr).set_slot(1, Tagged::null());
            let fn_ptr: *const () = primitives::iff as *const ();
            let fn_ptr_int = fn_ptr as i64;
            (*word_ptr).set_slot(2, tags);
            (*word_ptr).set_slot(3, Tagged::from_int(fn_ptr_int));
        }

        let quotation_array = ctx.gc.allocate_array(1);
        unsafe {
            let array_ptr = quotation_array.to_ptr() as *mut Array;
            (*array_ptr).set(0, word);
        }

        let quotation = ctx.gc.allocate_object(ctx.gc.specials.quotation_map);
        unsafe {
            let quotation_ptr = quotation.to_ptr();
            (*quotation_ptr).set_slot(0, Tagged::null());
            (*quotation_ptr).set_slot(1, quotation_array);
        }

        ctx.compile(&mut code_heap, quotation.to_ptr() as *const Quotation);

        let code = code_heap
            .get_code_for_quotation(quotation.to_ptr() as *const Quotation)
            .unwrap();

        assert_eq!(code.len(), 1);
        match code[0] {
            Code::CallPrimitive(_) => {}
            _ => panic!("Expected CallPrimitive operation"),
        }
    }

    #[test]
    fn test_compile_if_pattern() {
        let mut ctx = setup_context();
        let mut code_heap = CodeHeap::new();

        let true_array = ctx.gc.allocate_array(1);
        unsafe {
            let array_ptr = true_array.to_ptr() as *mut Array;
            (*array_ptr).set(0, Tagged::from_int(1));
        }

        let true_quotation =
            ctx.gc.allocate_object(ctx.gc.specials.quotation_map);
        unsafe {
            let quotation_ptr = true_quotation.to_ptr();
            (*quotation_ptr).set_slot(0, Tagged::null());
            (*quotation_ptr).set_slot(1, true_array);
        }

        let false_array = ctx.gc.allocate_array(1);
        unsafe {
            let array_ptr = false_array.to_ptr() as *mut Array;
            (*array_ptr).set(0, Tagged::from_int(0));
        }

        let false_quotation =
            ctx.gc.allocate_object(ctx.gc.specials.quotation_map);
        unsafe {
            let quotation_ptr = false_quotation.to_ptr();
            (*quotation_ptr).set_slot(0, Tagged::null());
            (*quotation_ptr).set_slot(1, false_array);
        }

        let if_name = ctx.gc.allocate_string("if");
        let if_word = ctx.gc.allocate_object(ctx.gc.specials.word_map);
        let tags = ctx.gc.allocate_array(1);

        unsafe {
            let tags_ptr = tags.to_ptr() as *mut Array;
            (*tags_ptr).set(0, ctx.gc.specials.primitive_tag);

            let word_ptr = if_word.to_ptr();
            (*word_ptr).set_slot(0, if_name);
            (*word_ptr).set_slot(1, Tagged::null());
            let fn_ptr: *const () = primitives::iff as *const ();
            let fn_ptr_int = fn_ptr as i64;
            (*word_ptr).set_slot(2, tags);
            (*word_ptr).set_slot(3, Tagged::from_int(fn_ptr_int));
        }

        let main_array = ctx.gc.allocate_array(3);
        unsafe {
            let array_ptr = main_array.to_ptr() as *mut Array;
            (*array_ptr).set(0, true_quotation);
            (*array_ptr).set(1, false_quotation);
            (*array_ptr).set(2, if_word);
        }

        let main_quotation =
            ctx.gc.allocate_object(ctx.gc.specials.quotation_map);
        unsafe {
            let quotation_ptr = main_quotation.to_ptr();
            (*quotation_ptr).set_slot(0, Tagged::null());
            (*quotation_ptr).set_slot(1, main_array);
        }

        ctx.compile(
            &mut code_heap,
            main_quotation.to_ptr() as *const Quotation,
        );

        let main_code = code_heap
            .get_code_for_quotation(main_quotation.to_ptr() as *const Quotation)
            .unwrap();
        let true_code = code_heap
            .get_code_for_quotation(true_quotation.to_ptr() as *const Quotation)
            .unwrap();
        let false_code =
            code_heap
                .get_code_for_quotation(
                    false_quotation.to_ptr() as *const Quotation
                )
                .unwrap();

        assert_eq!(main_code.len(), 1);
        match main_code[0] {
            Code::BranchInline(true_branch, false_branch) => {
                assert_eq!(
                    true_branch,
                    true_quotation.to_ptr() as *const Quotation
                );
                assert_eq!(
                    false_branch,
                    false_quotation.to_ptr() as *const Quotation
                );
            }
            _ => panic!("Expected BranchInline operation"),
        }

        assert_eq!(true_code.len(), 1);
        match true_code[0] {
            Code::Push(value) => assert_eq!(value.to_int(), 1),
            _ => panic!("Expected Push operation in true branch"),
        }

        assert_eq!(false_code.len(), 1);
        match false_code[0] {
            Code::Push(value) => assert_eq!(value.to_int(), 0),
            _ => panic!("Expected Push operation in false branch"),
        }
    }

    #[test]
    fn test_compile_reuse() {
        let mut ctx = setup_context();
        let mut code_heap = CodeHeap::new();

        let quotation_array = ctx.gc.allocate_array(1);
        unsafe {
            let array_ptr = quotation_array.to_ptr() as *mut Array;
            (*array_ptr).set(0, Tagged::from_int(42));
        }

        let quotation = ctx.gc.allocate_object(ctx.gc.specials.quotation_map);
        unsafe {
            let quotation_ptr = quotation.to_ptr();
            (*quotation_ptr).set_slot(0, Tagged::null());
            (*quotation_ptr).set_slot(1, quotation_array);
        }

        let first_node =
            ctx.compile(&mut code_heap, quotation.to_ptr() as *const Quotation);

        let second_node =
            ctx.compile(&mut code_heap, quotation.to_ptr() as *const Quotation);

        assert_eq!(first_node.as_ptr(), second_node.as_ptr());
    }

    #[test]
    fn test_compile_mixed_types() {
        let mut ctx = setup_context();
        let mut code_heap = CodeHeap::new();

        let word_name = ctx.gc.allocate_string("test_word");
        let word = ctx.gc.allocate_object(ctx.gc.specials.word_map);
        unsafe {
            let word_ptr = word.to_ptr();
            (*word_ptr).set_slot(0, word_name);
            (*word_ptr).set_slot(1, Tagged::null());
            (*word_ptr).set_slot(2, Tagged::null());
        }

        let str_obj = ctx.gc.allocate_string("test");

        let quotation_array = ctx.gc.allocate_array(4);
        unsafe {
            let array_ptr = quotation_array.to_ptr() as *mut Array;
            (*array_ptr).set(0, Tagged::from_int(42));
            (*array_ptr).set(1, str_obj);
            (*array_ptr).set(2, word);
            (*array_ptr).set(3, Tagged::null());
        }

        let quotation = ctx.gc.allocate_object(ctx.gc.specials.quotation_map);
        unsafe {
            let quotation_ptr = quotation.to_ptr();
            (*quotation_ptr).set_slot(0, Tagged::null());
            (*quotation_ptr).set_slot(1, quotation_array);
        }

        ctx.compile(&mut code_heap, quotation.to_ptr() as *const Quotation);

        let code = code_heap
            .get_code_for_quotation(quotation.to_ptr() as *const Quotation)
            .unwrap();

        assert_eq!(code.len(), 4);

        match code[0] {
            Code::Push(value) => assert_eq!(value.to_int(), 42),
            _ => panic!("Expected Push operation for integer"),
        }

        match code[1] {
            Code::Push(value) => unsafe {
                let str_ptr = value.to_ptr() as *const ByteArray;
                assert_eq!((*str_ptr).as_str(), "test");
            },
            _ => panic!("Expected Push operation for string"),
        }

        match code[2] {
            Code::Call(ref w) => unsafe {
                let name_ptr = w.name.to_ptr() as *const ByteArray;
                assert_eq!((*name_ptr).as_str(), "test_word");
            },
            _ => panic!("Expected Call operation for word"),
        }

        match code[3] {
            Code::Push(value) => assert_eq!(value, Tagged::null()),
            _ => panic!("Expected Push operation for null"),
        }
    }
}
