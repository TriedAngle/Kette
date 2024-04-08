use crate::objects::{Object, Word};
use std::mem;
// I might switch to register VM later, I just want working code for now :)
// stack bytecode and vm is so little effort it really doesn't matter tbh

#[repr(u8)]
#[derive(Debug, Clone, Copy)]
pub enum Instruction {
    NoOp,         // so we see no 0 in opcode
    PushSelf,     // pushes current objects pointer in methods
    PushInt,      // pushes integer (auto-converts to boxed)
    PushFloat,    // pushes float (auto-converts to boxed)
    PushObject,   // pushes any object
    Load,         // deref pointer (auto-boxes)
    Store,        // store value at pointer (auto-unboxes)
    Send,         // sends word to objct and autopops according to stack effect
    SendSelf,     // sends self ignore parents
    SendSuper,    // ignore self go to parent
    SendDelegate, // go to specific parent
    Return,       // pop callstack and return
}

#[repr(C)]
#[derive(Clone, Copy)]
pub union BytecodeValue {
    int: i64,
    float: f64,
    object: Object,
    pointer: usize,
    word: *const Word,
}

impl BytecodeValue {
    pub fn as_i64(self) -> i64 {
        unsafe { mem::transmute::<_, i64>(self) }
    }
}

unsafe impl Send for BytecodeValue {}
unsafe impl Sync for BytecodeValue {}

#[repr(packed)]
#[derive(Clone, Copy)]
pub struct Bytecode {
    pub instr: Instruction,
    pub value: BytecodeValue,
}

unsafe impl Send for Bytecode {}
unsafe impl Sync for Bytecode {}

impl Bytecode {
    pub const fn noop() -> Bytecode {
        Bytecode {
            instr: Instruction::NoOp,
            value: BytecodeValue { int: 0 },
        }
    }
    pub const fn push_self() -> Bytecode {
        Bytecode {
            instr: Instruction::PushSelf,
            value: BytecodeValue { int: 0 },
        }
    }
    pub const fn push_int(int: i64) -> Bytecode {
        Bytecode {
            instr: Instruction::PushInt,
            value: BytecodeValue { int },
        }
    }
    pub const fn push_float(float: f64) -> Bytecode {
        Bytecode {
            instr: Instruction::PushFloat,
            value: BytecodeValue { float },
        }
    }
    pub const fn push_object(object: Object) -> Bytecode {
        Bytecode {
            instr: Instruction::PushObject,
            value: BytecodeValue { object },
        }
    }
    pub const fn load(pointer: usize) -> Bytecode {
        Bytecode {
            instr: Instruction::Load,
            value: BytecodeValue { pointer },
        }
    }
    pub const fn store(pointer: usize) -> Bytecode {
        Bytecode {
            instr: Instruction::Store,
            value: BytecodeValue { pointer },
        }
    }
    pub const fn send(word: *const Word) -> Bytecode {
        Bytecode {
            instr: Instruction::Send,
            value: BytecodeValue { word },
        }
    }
    pub const fn send_self(word: *const Word) -> Bytecode {
        Bytecode {
            instr: Instruction::Send,
            value: BytecodeValue { word },
        }
    }
    pub const fn send_super(word: *const Word) -> Bytecode {
        Bytecode {
            instr: Instruction::Send,
            value: BytecodeValue { word },
        }
    }
    pub const fn send_delegate(word: *const Word) -> Bytecode {
        Bytecode {
            instr: Instruction::Send,
            value: BytecodeValue { word },
        }
    }
    pub const fn send_return() -> Bytecode {
        Bytecode {
            instr: Instruction::Return,
            value: BytecodeValue { int: 0 },
        }
    }
}

pub struct Code {
    data: *const Bytecode,
    top: *mut Bytecode,
    limit: *const Bytecode,
}

impl Code {
    pub fn new(data_ptr: *mut Bytecode, length: usize) -> Self {
        let limit_ptr = unsafe { data_ptr.add(length) };

        Code {
            data: data_ptr,
            top: data_ptr,
            limit: limit_ptr,
        }
    }

    pub fn push(&mut self, bytecode: Bytecode) -> Result<(), ()> {
        unsafe {
            if self.top as *const _ < self.limit {
                self.top.write(bytecode);
                self.top = self.top.add(1);
                Ok(())
            } else {
                Err(())
            }
        }
    }
}

pub struct CodeIterator {
    current: *const Bytecode,
    limit: *const Bytecode,
}

impl Code {
    pub fn iter(&self) -> CodeIterator {
        CodeIterator {
            current: self.data,
            limit: self.limit,
        }
    }
}

impl Iterator for CodeIterator {
    type Item = Bytecode;

    fn next(&mut self) -> Option<Self::Item> {
        if self.current < self.limit {
            unsafe {
                let item = *self.current;
                self.current = self.current.add(1);
                Some(item)
            }
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use std::ptr;

    use super::*;

    #[test]
    fn instruction_size() {
        assert_eq!(mem::size_of::<Bytecode>(), 9);
    }

    #[test]
    fn push_instructions() {
        let mut bytecodes = vec![Bytecode::noop(); 4]; // example initialization
        let mut code = Code::new(bytecodes.as_mut_ptr(), bytecodes.len());
        let _res = code.push(Bytecode::push_int(666));
        let _res = code.push(Bytecode::push_int(31672));
        let _res = code.push(Bytecode::send(ptr::null()));
        let _res = code.push(Bytecode::store(0));

        for bc in code.iter() {
            println!("Instruction: {:?}, {:?}", bc.instr, bc.value.as_i64());
        }
    }
}
