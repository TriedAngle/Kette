#![allow(dead_code, unused)]

use std::collections::{HashMap, HashSet};

use bytecode::Code;
use objects::Word;

mod allocators;
mod bytecode;
mod objects;

struct CodeHeap {
    pub new: HashSet<*const Word>,
    pub compiled: HashMap<*const Word, Code>,
}

struct VM {}
