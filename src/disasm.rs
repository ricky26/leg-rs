use std::fmt;
use std::convert;

use super::{
    Register, ImmOrReg, ExecutionContext, InstructionFlags,
    Shift, ShiftType, Result, Error,
    INST_NORMAL, INST_SET_FLAGS, INST_BYTE, INST_HALF, INST_WIDE,
};

pub struct Disassembler<'a>(&'a mut fmt::Write);


impl<'a> Disassembler<'a> {
    pub fn new(fmt: &'a mut fmt::Write) -> Disassembler<'a> {
        Disassembler(fmt)
    }
}

impl<'a> ExecutionContext for Disassembler<'a> {
    fn undefined(&mut self) -> Result<()> {
        try!(writeln!(self.0, "undefined instruction"));
        Ok(())
    }
    
    fn unpredictable(&mut self) -> Result<()> {
        try!(writeln!(self.0, "unpredictable instruction"));
        Ok(())
    }
    
    // Move
    fn mov(&mut self, flags: InstructionFlags, dest: Register, src: ImmOrReg<i32>, shift: Shift) -> Result<()> {
        try!(writeln!(self.0, "MOV{} {}, {}{}", flags, dest, src, shift));
        Ok(())
    }
    fn adr(&mut self, dest: Register, offset: ImmOrReg<i32>) -> Result<()> {
        try!(writeln!(self.0, "ADR {}, {}", dest, offset));
        Ok(())
    }

    fn add(&mut self, flags: InstructionFlags, dest: Register, src: ImmOrReg<i32>, add: ImmOrReg<i32>) -> Result<()> {
        try!(writeln!(self.0, "ADD{} {}, {}, {}", flags, dest, src, add));
        Ok(())
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

impl fmt::Display for Shift {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &Shift(ShiftType::None, x) => x.fmt(fmt),
            &Shift(ShiftType::LSL, x) => write!(fmt, " LSL {}", x),
            &Shift(ShiftType::LSR, x) => write!(fmt, " LSR {}", x),
            &Shift(ShiftType::ASR, x) => write!(fmt, " ASR {}", x),
            &Shift(ShiftType::ROR, x) => write!(fmt, " ROR {}", x),
            &Shift(ShiftType::RRX, x) => write!(fmt, " RRX {}", x),
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
        
        if (*self & INST_HALF) != INST_NORMAL {
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

impl convert::From<fmt::Error> for Error {
    fn from(_src: fmt::Error) -> Error {
        Error::Unknown
    }
}
