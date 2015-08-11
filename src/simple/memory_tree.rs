use std::{cmp, sync, cell};

use super::Memory;
use super::super::*;

#[derive(Copy, Clone, Debug)]
struct Bound(u64, u64);

impl Bound {
    fn contains(&self, addr: u64) -> bool {
        (self.0 <= addr) && (addr <= self.1)
    }
}

struct Entry<'a>(Bound, Box<Memory+'a>);

pub struct MemoryTree<'a> {
    dirty: cell::Cell<bool>,
    contents: sync::RwLock<Vec<Entry<'a>>>,
}

impl<'a> MemoryTree<'a> {
    pub fn new() -> MemoryTree<'a> {
        MemoryTree {
            dirty: cell::Cell::new(false),
            contents: sync::RwLock::new(Vec::new()),
        }
    }

    pub fn with_mem<F, T>(&self, addr: u64, f: F) -> Option<T>
        where F: FnOnce(u64, &Memory) -> T
    {
        if self.dirty.get() {
            self.dirty.set(false);
            self.contents.write().and_then(|mut x| {
                x.sort_by(|x, y| (x.0).0.cmp(&(y.0).0));
                Ok(())
            }).ok();
        }

        let contents = match self.contents.read() {
            Ok(x) => x,
            _ => { return None },
        };

        let idx = contents.binary_search_by(|x: &Entry| {
            if x.0.contains(addr) {
                cmp::Ordering::Equal
            } else {
                (x.0).0.cmp(&addr)
            }
        });
        
        match idx {
            Ok(idx) => {
                let entry: &Entry<'a> = &contents[idx];
                Some(f((entry.0).0, &*entry.1))
            },
            _ => None,
        }
    }

    pub fn add(&mut self, addr: u64, len: u32, mem: Box<Memory + 'a>) {
        let bound = Bound(addr, addr + (len as u64));
        self.contents.write().unwrap().push(Entry(bound, mem));
        self.dirty.set(true);
    }
}

impl<'a> super::Memory for MemoryTree<'a> {
    fn read(&self, addr: u64, dest: &mut [u8]) -> Result<()> {
        self.with_mem(addr, |base, mem| mem.read(addr - base, dest)).unwrap_or(Err(Error::Unknown(format!("invalid memory read"))))
    }
    
    fn write(&self, addr: u64, src: &[u8]) -> Result<()> {
        self.with_mem(addr, |base, mem| mem.write(addr - base, src)).unwrap_or(Err(Error::Unknown(format!("invalid memory write"))))
    }
}
