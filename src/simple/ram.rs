use std::cmp;
use std::sync;

use super::super::*;

pub struct RAM {
    pub storage: sync::RwLock<Vec<u8>>,
}

impl RAM {
    pub fn with_capacity(capacity: usize) -> RAM {
        RAM {
            storage: sync::RwLock::new(vec![0u8; capacity]),
        }
    }
}

impl super::Memory for RAM {
    fn read(&self, addr: u64, dest: &mut [u8]) -> Result<()> {
        let storage = match self.storage.read() {
            Ok(x) => x,
            _ => { return Err(Error::Unknown(format!("failed to read from RAM"))) },
        };
        
        let addr = addr as usize;
        let mem_size = storage.len();

        if addr < mem_size {
            let start = cmp::min(mem_size, addr);
            let end = cmp::min(mem_size, addr + dest.len());

            super::copy_memory(&storage[start..end], dest);
            Ok(())
        } else {
            Err(Error::Unknown(format!("tried to read invalid RAM address 0x{:x}", addr)))
        }
    }

    fn write(&self, addr: u64, src: &[u8]) -> Result<()> {
        let mut storage = match self.storage.write() {
            Ok(x) => x,
            _ => { return Err(Error::Unknown(format!("failed to write to RAM"))) },
        };
        
        let addr = addr as usize;
        let mem_size = storage.len();

        if addr < mem_size {
            let start = cmp::min(mem_size, addr);
            let end = cmp::min(mem_size, addr + src.len());

            super::copy_memory(src, &mut storage[start..end]);
            Ok(())
        } else {
            Err(Error::Unknown(format!("tried to write invalid RAM address 0x{:x}", addr)))
        }
    }
}

