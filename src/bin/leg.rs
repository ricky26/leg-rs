extern crate leg;
extern crate docopt;

use std::io::Read;
use leg::simple::Memory;
use docopt::Docopt;

static USAGE: &'static str = "
Usage: leg [options] <executable>...

Options:
    -p                            Pause at startup.
    -g <addr>, --gdb=<addr>       Listen for GDB connections on GDBADDR (for example 0.0.0.0:8084)
";

fn main() {
    let mut gdbserver = leg::gdb::Server::new();
    let mut emu = leg::simple::SimpleEmulator::new(leg::simple::MemoryTree::new());

    emu.memory.add(0, 0x1000, Box::new(leg::simple::RAM::with_capacity(0x1000)));
    
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
        let (path, addr) = if let Some(_) = arg.find('@') {
            let parts: Vec<_> = arg.splitn(2, '@').collect();
            (parts[0], u64::from_str_radix(&parts[1], 10).unwrap())
        } else {
            (arg, 0u64)
        };
        
        let vec = {
            let mut f = std::fs::File::open(path).unwrap();
            let mut vec = Vec::new();
            f.read_to_end(&mut vec).ok();
            vec
        };

        emu.memory.write(addr, &vec).ok();
    }

    loop {
        match emu.execute_one() {
            Err(x) => {
                println!("ERROR {:?}", x);
                if emu.debugging() {
                    emu.set_paused(true);
                    emu.send_gdb_command(&leg::gdb::Command::new("S05"));
                } else {
                    emu.print_state().ok();
                    break
                }
            },
            _ => {},
        }
        
        gdbserver.process_commands(|x| emu.process_gdb_command(x));
        emu.with_pending_gdb_commands(|x| gdbserver.send_command(x));
    }
}
