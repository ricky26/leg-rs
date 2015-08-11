use super::{System, MemoryTree};

pub struct SimpleSystem<'a> {
    pub memory: MemoryTree<'a>,
}

impl<'a> SimpleSystem<'a> {
    pub fn new() -> SimpleSystem<'a> {
        SimpleSystem {
            memory: MemoryTree::new(),
        }
    }
}

impl<'a> System for SimpleSystem<'a> {
    type Memory = MemoryTree<'a>;
    
    fn memory(&self) -> &MemoryTree<'a> {
        &self.memory
    }
}
