extern crate leg;

struct Memory([u8;128]);

fn copy_memory(src: &[u8], dest: &mut [u8]) {
    for x in 0.. {
        if (x >= src.len()) || (x >= dest.len()) {
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
    
    
    emu.set_register(leg::Register::R0, 20);
    emu.set_register(leg::Register::R4, 22);
    println!("{:?}", leg::thumb::execute(&mut emu, &[0x19, 0x00]));
    println!("{:?}", emu.register(leg::Register::R0));

    
    copy_memory(&[0xb5, 0x80,
                  0xaf, 0x00,
                  0x46, 0xbd,
                  0xbd, 0x80],
                &mut emu.memory.0[0..8]);
    println!("{:?}", emu.execute());
    
    let mut disas = String::new();
    println!("{:?}", leg::thumb::disassemble(&mut disas, &[0xb5, 0x80,
                                                           0xaf, 0x00,
                                                           0x46, 0xbd,
                                                           0xbd, 0x80]));
    println!("{}", disas);
}
