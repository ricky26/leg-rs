use std::cmp;

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
    dirty: bool,
    contents: Vec<Entry<'a>>,
}

impl<'a> MemoryTree<'a> {
    pub fn new() -> MemoryTree<'a> {
        MemoryTree {
            dirty: false,
            contents: Vec::new(),
        }
    }

    pub fn find_mut(&mut self, addr: u64) -> Option<(u64, &mut Memory)> {
        if self.dirty {
            self.dirty = false;
            self.contents.sort_by(|x, y| (x.0).0.cmp(&(y.0).0));
        }
        
        match self.contents.as_mut().binary_search_by(|x| {
            if x.0.contains(addr) {
                cmp::Ordering::Equal
            } else {
                (x.0).0.cmp(&addr)
            }
        }) {
            Ok(idx) => {
                let entry: &mut Entry<'a> = &mut self.contents[idx];
                Some(((entry.0).0, &mut *entry.1))
            },
            _ => None,
        }
    }

    pub fn add(&mut self, addr: u64, len: u32, mem: Box<Memory + 'a>) {
        let bound = Bound(addr, addr + (len as u64));
        self.contents.push(Entry(bound, mem));
        self.dirty = true;
    }
}

impl<'a> super::Memory for MemoryTree<'a> {
    fn read(&mut self, addr: u64, dest: &mut [u8]) -> Result<()> {
        if let Some((base, mem)) = self.find_mut(addr) {
            mem.read(addr - base, dest)
        } else {
            Err(Error::Undefined("invalid memory read".into()))
        }
    }
    
    fn write(&mut self, addr: u64, src: &[u8]) -> Result<()> {
        if let Some((base, mem)) = self.find_mut(addr) {
            mem.write(addr - base, src)
        } else {
            Err(Error::Undefined("invalid memory read".into()))
        }
    }
}
