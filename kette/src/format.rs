use crate::{
    Array, ByteArray, Handle, HeapValue, Interpreter, Message, ObjectType,
    Quotation, Selector, SlotDescriptor, SlotObject, SlotTags, Value,
};
use std::{fmt::Write, ops::Deref};

const DEFAULT_MAX_DEPTH: usize = 2;

impl Interpreter {
    /// Prints the current stack state to stdout.
    pub fn print_stack(&mut self) {
        let depth = self.state.depth();
        println!("--- Datastack ({}):", depth);

        if depth == 0 {
            return;
        }

        let sel_name = self.vm.intern_string(">string", &mut self.heap);
        let selector = Selector::new(sel_name, self.vm.shared.clone());

        for i in 0..depth {
            let val = unsafe { self.state.stack_get_nth_unchecked(i) };

            // Use the default max depth for stack printing
            let pretty = self.pretty_print_internal(
                val,
                0,
                DEFAULT_MAX_DEPTH,
                &selector,
            );

            println!("[{:02}] {}", depth - i - 1, pretty);
        }
    }

    pub fn stack_to_string(&mut self) -> String {
        let depth = self.state.depth();
        let sel_name = self.vm.intern_string(">string", &mut self.heap);
        let selector = Selector::new(sel_name, self.vm.shared.clone());

        let mut output = String::new();
        for i in 0..depth {
            let val = unsafe { self.state.stack_get_nth_unchecked(i) };

            // Use the default max depth for stack printing
            let pretty = self.pretty_print_internal(
                val,
                0,
                DEFAULT_MAX_DEPTH,
                &selector,
            );

            let _ = writeln!(&mut output, "[{:02}] {}", depth - i - 1, pretty);
        }
        output
    }

    /// Public API now accepts a max_depth argument
    pub fn pretty_print_value(
        &mut self,
        value: Value,
        recursion_depth: usize,
        max_depth: usize,
    ) -> String {
        let sel_name = self.vm.intern_string(">string", &mut self.heap);

        let selector = Selector::new(sel_name, self.vm.shared.clone());

        self.pretty_print_internal(value, recursion_depth, max_depth, &selector)
    }

    /// Internal recursive function that takes an existing Selector to avoid re-interning.
    fn pretty_print_internal(
        &mut self,
        value: Value,
        current_depth: usize,
        max_depth: usize,
        selector: &Selector,
    ) -> String {
        // Compare current depth against the passed max_depth
        if current_depth > max_depth {
            return "...".to_string();
        }

        self.pretty_print_structural(value, current_depth, max_depth, selector)
    }

    fn pretty_print_structural(
        &mut self,
        value: Value,
        depth: usize,
        max_depth: usize,
        selector: &Selector,
    ) -> String {
        if let Some(fixnum) = value.as_tagged_fixnum::<i64>() {
            return format!("{}", fixnum.as_i64());
        }

        if let Some(handle) = value.as_tagged_object::<HeapValue>() {
            let heap_obj = unsafe { handle.promote_to_handle() };

            match heap_obj.header.object_type() {
                Some(ObjectType::Slot) => unsafe {
                    self.format_slot_object(
                        heap_obj.cast(),
                        depth,
                        max_depth,
                        selector,
                    )
                },
                Some(ObjectType::Array) => unsafe {
                    self.format_array(
                        heap_obj.cast(),
                        depth,
                        max_depth,
                        selector,
                    )
                },
                Some(ObjectType::ByteArray) => unsafe {
                    self.format_byte_array(heap_obj.cast())
                },
                Some(ObjectType::Float) => unsafe {
                    self.format_float(heap_obj.cast())
                },
                Some(ObjectType::Quotation) => unsafe {
                    self.format_quotation(
                        heap_obj.cast(),
                        depth,
                        max_depth,
                        selector,
                    )
                },
                Some(ObjectType::Message) => unsafe {
                    self.format_message(heap_obj.cast())
                },
                _ => {
                    format!(
                        "<Object type={:?} @ {:p}>",
                        heap_obj.header.object_type(),
                        heap_obj.as_ptr()
                    )
                }
            }
        } else {
            "<Unknown Value>".to_string()
        }
    }

    unsafe fn format_array(
        &mut self,
        array: Handle<Array>,
        depth: usize,
        max_depth: usize,
        selector: &Selector,
    ) -> String {
        let size = array.size();
        if size == 0 {
            return "{ }".to_string();
        }

        let mut out = String::new();
        out.push_str("{ ");

        for i in 0..size {
            let val = unsafe { array.get_unchecked(i) };

            // Pass max_depth through to the recursive call
            out.push_str(&self.pretty_print_internal(
                val,
                depth + 1,
                max_depth,
                selector,
            ));

            if i < size - 1 {
                out.push_str(" . ");
            }
        }

        out.push_str(" }");
        out
    }

    unsafe fn format_slot_object(
        &mut self,
        object: Handle<SlotObject>,
        depth: usize,
        max_depth: usize,
        selector: &Selector,
    ) -> String {
        let map = object.map;
        let slots = map.slots();

        let data_slots: Vec<&SlotDescriptor> =
            slots.iter().filter(|s| s.is_data_consumer()).collect();

        if data_slots.is_empty() {
            return "(| |)".to_string();
        }

        let mut out = String::new();
        out.push_str("(| ");

        for (i, slot_desc) in data_slots.iter().enumerate() {
            let name_bytes = slot_desc.name.as_bytes();
            let name_str = std::str::from_utf8(name_bytes).unwrap_or("???");

            out.push_str(name_str);
            out.push_str(":= ");

            // Get the value
            let val = if slot_desc.tags().contains(SlotTags::ASSIGNABLE) {
                let offset_val = slot_desc.value;
                if let Some(offset) = offset_val.as_tagged_fixnum::<usize>() {
                    unsafe { object.get_slot_unchecked(offset.into()) }
                } else {
                    Value::zero()
                }
            } else {
                slot_desc.value
            };

            // Pass max_depth through to the recursive call
            out.push_str(&self.pretty_print_internal(
                val,
                depth + 1,
                max_depth,
                selector,
            ));

            if i < data_slots.len() - 1 {
                out.push_str(" . ");
            }
        }

        out.push_str(" |)");
        out
    }

    unsafe fn format_byte_array(&self, ba: Handle<ByteArray>) -> String {
        let bytes = ba.as_bytes();
        if bytes.is_empty() {
            return "[]".to_string();
        }

        let mut out = String::new();
        out.push('[');
        for b in bytes {
            write!(&mut out, " {:02X}", b).unwrap();
        }
        out.push_str(" ]");
        out
    }

    unsafe fn format_float(&self, f: Handle<crate::Float>) -> String {
        format!("{}", f.value)
    }

    unsafe fn format_message(&self, m: Handle<Message>) -> String {
        let name = m.value;
        let bytes = name.as_bytes();
        let s = std::str::from_utf8(bytes).unwrap_or("???");
        format!("{}", s)
    }

    unsafe fn format_quotation(
        &mut self,
        quotation: Handle<Quotation>,
        depth: usize,
        max_depth: usize,
        selector: &Selector,
    ) -> String {
        let map = quotation.map;

        // Check if the map has associated code
        if !map.has_code() {
            return "[ <native/empty> ]".to_string();
        }

        // Dereference the code handle to access the structure
        let code = map.code.deref();

        // The `body` field holds the Array of source tokens/values
        let body_array = code.body;
        let size = body_array.size();

        if size == 0 {
            return "[ ]".to_string();
        }

        let mut out = String::new();
        out.push_str("[ ");

        for i in 0..size {
            let val = unsafe { body_array.get_unchecked(i) };

            // Recursively print the body element, passing max_depth
            out.push_str(&self.pretty_print_internal(
                val,
                depth + 1,
                max_depth,
                selector,
            ));

            // Space separator (no dots or commas for quotations)
            if i < size - 1 {
                out.push(' ');
            }
        }

        out.push_str(" ]");
        out
    }
}
