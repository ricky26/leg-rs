extern crate leg;
use std::io::Read;

struct Memory([u8;128]);

fn copy_memory(src: &[u8], dest: &mut [u8]) {
    for x in 0.. {
        if (x >= src.len()) || (x >= dest.len()) {
            println!("exiting at {}", x);
            break
        }

        dest[x] = src[x]
    }
}

impl leg::simple::Memory for Memory {
    fn read(&self, addr: u64, dest: &mut [u8]) -> leg::Result<()> {
        let addr = addr as usize;
        if addr >= 128 {
            return Err(leg::Error::Unknown)
        }
        
        let start = std::cmp::min(128, addr);
        let end = std::cmp::min(128, addr + dest.len());
        println!("read {} -> {}", start, end);
        copy_memory(&self.0[start..end], dest);
        Ok(())
    }
    fn write(&mut self, addr: u64, src: &[u8]) -> leg::Result<()> {
        let addr = addr as usize;
        if addr >= 128 {
            return Err(leg::Error::Unknown)
        }
        
        let start = std::cmp::min(128, addr);
        let end = std::cmp::min(128, addr + src.len());
        println!("write {} -> {}", start, end);
        copy_memory(src, &mut self.0[start..end]);
        Ok(())
    }
}

fn main() {
    let mut emu = leg::simple::SimpleEmulator::<Memory>::new(Memory([0u8;128]));

    let vec = {
        let mut f = std::fs::File::open(std::env::args().next().unwrap()).unwrap();
        let mut vec = Vec::new();
        f.read_to_end(&mut vec);
        vec
    };

    copy_memory(&vec, &mut emu.memory.0);
    println!("{:?}", emu.execute());
}
