extern crate leg;
extern crate docopt;

use std::io::Read;
use docopt::Docopt;

struct Memory([u8;4096]);

static USAGE: &'static str = "
Usage: leg [options] <executable>

Options:
    -p                            Pause at startup.
    -g <addr>, --gdb=<addr>       Listen for GDB connections on GDBADDR (for example 0.0.0.0:8084)
";

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
        let mem_size = std::mem::size_of_val(&self.0);
        
        if addr >= mem_size {
            return Err(leg::Error::Unknown(format!("tried to read invalid address 0x{:x}", addr)));
        }
        
        let start = std::cmp::min(mem_size, addr);
        let end = std::cmp::min(mem_size, addr + dest.len());
        copy_memory(&self.0[start..end], dest);
        Ok(())
    }
    fn write(&mut self, addr: u64, src: &[u8]) -> leg::Result<()> {
        let addr = addr as usize;
        let mem_size = std::mem::size_of_val(&self.0);
        
        if addr >= mem_size {
            return Err(leg::Error::Unknown(format!("tried to read invalid address 0x{:x}", addr)));
        }
        
        let start = std::cmp::min(mem_size, addr);
        let end = std::cmp::min(mem_size, addr + src.len());
        copy_memory(src, &mut self.0[start..end]);
        Ok(())
    }
}

fn main() {
    let mut gdbserver = leg::gdb::Server::new();
    let mut emu = leg::simple::SimpleEmulator::<Memory>::new(Memory([0u8;4096]));
    
    let args = Docopt::new(USAGE)
        .and_then(|d| d.argv(std::env::args()).parse())
        .unwrap_or_else(|e| e.exit());

    emu.set_register(leg::Register::SP, 4096);
    emu.set_paused(args.get_bool("-p"));

    let listen = args.get_str("-g");
    if listen != "" {
        gdbserver.start_listening(listen);
    }

    for arg in args.get_vec("<executable>") {
        let vec = {
            let mut f = std::fs::File::open(arg).unwrap();
            let mut vec = Vec::new();
            f.read_to_end(&mut vec).ok();
            vec
        };

        copy_memory(&vec, &mut emu.memory.0);
    }

    loop {
        match emu.execute_one() {
            Err(x) => {
                println!("ERROR {:?}", x);
                if emu.debugging() {
                    emu.set_paused(true);
                    emu.send_gdb_command(&leg::gdb::Command::new("S05"));
                } else {
                    break
                }
            },
            _ => {},
        }
        
        gdbserver.process_commands(|x| emu.process_gdb_command(x));
        emu.with_pending_gdb_commands(|x| gdbserver.send_command(x));
    }
}
