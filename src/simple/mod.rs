//! A 'simple' ARM emulator.
//!
//! At the moment the emulator only has support for a handful of THUMB-2 instructions
/// and no ARM-mode support.

use super::*;

pub use self::memory_tree::MemoryTree;
pub use self::ram::RAM;
pub use self::emu::SimpleEmulator;
pub use self::system::SimpleSystem;

pub mod memory_tree;
pub mod ram;
pub mod emu;
pub mod system;

/// Copy as much memory as possible from `src` to `dest`.
pub fn copy_memory(src: &[u8], dest: &mut [u8]) {
    for x in 0.. {
        if (x >= src.len()) || (x >= dest.len()) {
            break
        }

        dest[x] = src[x]
    }
}

fn swap_word(src: Word) -> Word {
    let src = src as u32;
    let src = (src >> 24)
        | ((src >> 8) & 0xff00)
        | ((src << 8) & 0xff0000)
        | ((src << 24) & 0xff000000);
    src as Word
}

fn adc32(a: Word, b: Word, c: Word) -> (Word, bool, bool) {
    let sa = a as i64;
    let sb = b as i64;
    let sc = c as i64;
    let ua = (a as u32) as u64;
    let ub = (b as u32) as u64;
    let uc = (c as u32) as u64;
    
    let us = ua.wrapping_add(ub).wrapping_add(uc);
    let ss = sa.wrapping_add(sb).wrapping_add(sc);
    let result = us as u32;

    (result as i32,
     (result as u64) != us,
     ((result as i32) as i64) != ss)
}

pub trait Memory {
    fn read(&self, _addr: u64, _dest: &mut [u8]) -> Result<()> { Err(Error::Unknown(format!("not implemented"))) }
    fn write(&self, _addr: u64, _src: &[u8]) -> Result<()> { Err(Error::Unknown(format!("not implemented"))) }

    fn read_u8(&self, addr: u64) -> Result<u8> {
        let mut data = [0u8];
        try!(self.read(addr, &mut data));
        Ok(data[0])
    }

    fn read_u16(&self, addr: u64) -> Result<u16> {
        let mut data = [0u8;2];
        try!(self.read(addr, &mut data));
        Ok((data[0] as u16) | ((data[1] as u16) << 8))
    }

    fn read_u32(&self, addr: u64) -> Result<u32> {
        let mut data = [0u8;4];
        try!(self.read(addr, &mut data));
        Ok((data[0] as u32)
           | ((data[1] as u32) << 8)
           | ((data[2] as u32) << 16)
           | ((data[3] as u32) << 24))
    }

    fn write_u8(&self, addr: u64, val: u8) -> Result<()> {
        self.write(addr, &[val])
    }

    fn write_u16(&self, addr: u64, val: u16) -> Result<()> {
        self.write(addr, &[(val & 0xff) as u8,
                           ((val >> 8) & 0xff) as u8])
    }

    fn write_u32(&self, addr: u64, val: u32) -> Result<()> {
        self.write(addr, &[(val & 0xff) as u8,
                           ((val >> 8) & 0xff) as u8,
                           ((val >> 16) & 0xff) as u8,
                           ((val >> 24) & 0xff) as u8])
    }
}

pub trait System {
    type Memory: Memory;
    
    fn memory(&self) -> &Self::Memory;
}
