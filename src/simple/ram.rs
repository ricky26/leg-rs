use std::cmp;

use super::super::*;

pub struct RAM {
    pub storage: Vec<u8>,
}

impl RAM {
    pub fn with_capacity(capacity: usize) -> RAM {
        RAM {
            storage: vec![0u8; capacity],
        }
    }
}

impl super::Memory for RAM {
    fn read(&mut self, addr: u64, dest: &mut [u8]) -> Result<()> {
        let addr = addr as usize;
        let mem_size = self.storage.len();

        if addr < mem_size {
            let start = cmp::min(mem_size, addr);
            let end = cmp::min(mem_size, addr + dest.len());

            super::copy_memory(&self.storage[start..end], dest);
            Ok(())
        } else {
            Err(Error::Unknown(format!("tried to read invalid RAM address 0x{:x}", addr)))
        }
    }

    fn write(&mut self, addr: u64, src: &[u8]) -> Result<()> {
        let addr = addr as usize;
        let mem_size = self.storage.len();

        if addr < mem_size {
            let start = cmp::min(mem_size, addr);
            let end = cmp::min(mem_size, addr + src.len());

            super::copy_memory(src, &mut self.storage[start..end]);
            Ok(())
        } else {
            Err(Error::Unknown(format!("tried to write invalid RAM address 0x{:x}", addr)))
        }
    }
}

