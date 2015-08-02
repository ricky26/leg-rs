use std::fmt;

use super::{
    Register, ImmOrReg, ExecutionContext, InstructionFlags,
    INST_NORMAL, INST_SET_FLAGS, INST_BYTE, INST_WORD, INST_WIDE,
};

pub struct Disassembler<'a>(&'a mut fmt::Write);


impl<'a> Disassembler<'a> {
    pub fn new(fmt: &'a mut fmt::Write) -> Disassembler<'a> {
        Disassembler(fmt)
    }
}

impl<'a> ExecutionContext for Disassembler<'a> {
    fn undefined(&mut self) { writeln!(self.0, "undefined instruction").ok(); }
    fn unpredictable(&mut self) { writeln!(self.0, "unpredictable instruction").ok(); }
    
    // Move
    fn mov(&mut self, flags: InstructionFlags, dest: Register, src: ImmOrReg<i32>) {
        writeln!(self.0, "MOV{} {}, {}", flags, dest, src).ok();
    }
    fn adr(&mut self, dest: Register, offset: ImmOrReg<i32>) {
        writeln!(self.0, "ADR {}, {}", dest, offset).ok();
    }

    fn add(&mut self, flags: InstructionFlags, dest: Register, src: ImmOrReg<i32>, add: ImmOrReg<i32>) {
        writeln!(self.0, "ADD{} {}, {}, {}", flags, dest, src, add).ok();
    }
}

impl fmt::Display for Register {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        fmt.write_str(self.name())
    }
}

impl<T: fmt::Display> fmt::Display for ImmOrReg<T> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &ImmOrReg::Reg(ref x) => x.fmt(fmt),
            &ImmOrReg::Imm(ref x) => write!(fmt, "#{}", x),
        }
    }
}

impl fmt::Display for InstructionFlags {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        if (*self & INST_SET_FLAGS) != INST_NORMAL {
            try!(fmt.write_str("S"))
        }

        if (*self & INST_BYTE) != INST_NORMAL {
            try!(fmt.write_str("B"))
        }
        
        if (*self & INST_WORD) != INST_NORMAL {
            try!(fmt.write_str("H"))
        }
        
        if (*self & INST_WIDE) == INST_NORMAL {
            //try!(fmt.write_str(".N"))
        } else {
            try!(fmt.write_str(".W"))
        }

        Ok(())
    }
}
