// Parser for the THUMB-2 instruction set

use std::fmt;

use super::*;
use super::disasm::Disassembler;

/// Execute up to one THUMB instruction.
pub fn execute<'a, 'b, T : ExecutionContext>(context: &'b mut T, mut buffer: &'a [u8]) -> (&'a [u8], Result<()>) {
    if buffer.len() < 4  {
        return (buffer, Err(Error::NotEnoughInput(4)))
    }

    match execute_32(buffer[3] as u32
                     | ((buffer[2] as u32) << 8)
                     | ((buffer[1] as u32) << 16)
                     | ((buffer[0] as u32) << 24),
                     context) {
        Err(x) => return (buffer, Err(x)),
        _ => buffer = &buffer[4..],
    }

    (buffer, Ok(()))
}

/// Disassemble some ARM code.
pub fn disassemble<'a, 'b>(fmt: &'b mut fmt::Write, mut buffer: &'a [u8]) -> (&'a [u8], Result<()>) {
    loop {
        if buffer.len() == 0 {
            return (buffer, Ok(()))
        }
        
        let err = match execute(&mut Disassembler::new(fmt), buffer) {
            (b, e) => { buffer = b; e },
        };
        if let Err(Error::NotEnoughInput(_)) = err {
            return (buffer, err)
        }
    }
}

/// Execute a ARM instruction as an integer.
pub fn execute_32<T: ExecutionContext>(src: u32, context: &mut T) -> Result<()> {
    //let s32 = src as i32;
    
    match src &! 0xfffffff {
        //
        // Data-processing and miscellaneous instructions
        //
        
        _ => context.undefined("arm"),
    }
}
