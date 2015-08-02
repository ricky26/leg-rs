use std::{mem, result, error, fmt};

#[macro_use]
extern crate bitflags;


bitflags! {
    flags InstructionFlags: u8 {
        const INST_NORMAL         = 0,

        const INST_SET_FLAGS      = 1 << 0,
        const INST_WORD           = 1 << 1,
        const INST_BYTE           = 1 << 3,
        const INST_SIGNED         = 1 << 4,
        const INST_WIDE           = 1 << 5,
    }
}

fn register(src: i8) -> Register {
    Register::from_index(src).expect("invalid register index")
}

fn condition(src: i8) -> Condition {
    Condition::from_index(src).expect("invalid condition index")
}

#[derive(Debug,Copy,Clone)]
pub enum ImmOrReg<T> {
    Imm(T),
    Reg(Register),
}

impl<T> ImmOrReg<T> {
    pub fn register(idx: i8) -> ImmOrReg<T> {
        ImmOrReg::Reg(register(idx))
    }

    pub fn imm(value: T) -> ImmOrReg<T> {
        ImmOrReg::Imm(value)
    }
}

/// Enum of all 32-bit ARM registers.
#[derive(Debug,Copy,Clone,PartialEq,Eq)]
pub enum Register {
    R0,
    R1,
    R2,
    R3,
    R4,
    R5,
    R6,
    R7,
    R8,
    R9,
    R10,
    R11,
    R12,
    SP,  // R13
    LR,  // R14
    PC,  // R15
}

impl Register {
    /// Convert from R{x} index, to enum value.
    pub fn from_index(idx: i8) -> Option<Register> {
        if idx < 16 {
            Some(unsafe { mem::transmute(idx) })
        } else {
            None
        }
    }

    /// Convert from enum value to R{x} index.
    /// This will be a return value between 0 and 0b1111.
    pub fn index(&self) -> i8 {
        *self as i8
    }

    /// Get assembly name for this register.
    pub fn name(&self) -> &'static str {
        match self {
            &Register::R0  => "r0",
            &Register::R1  => "r1",
            &Register::R2  => "r2",
            &Register::R3  => "r3",
            &Register::R4  => "r4",
            &Register::R5  => "r5",
            &Register::R6  => "r6",
            &Register::R7  => "r7",
            &Register::R8  => "r8",
            &Register::R9  => "r9",
            &Register::R10 => "r10",
            &Register::R11 => "r11",
            &Register::R12 => "r12",
            &Register::SP  => "sp",
            &Register::LR  => "lr",
            &Register::PC  => "pc",
        }
    }
}

/// Condition.
#[derive(Copy,Clone,PartialEq,Eq)]
pub enum Condition {
    /// Equal
    EQ,
    /// Not Equal
    NE,
    /// Carry Set
    CS,
    /// Carry Clear
    CC,
    /// Minus
    MI,
    /// Positive
    PL,
    /// Overflow Set
    VS,
    /// Overflow Clear
    VC,
    /// Unsigned Greater Than
    HI,
    /// Unsigned Less Than or Equal
    LS,
    /// Greater Than or Equal
    GE,
    /// Less Than
    LT,
    /// Greater Than
    GT,
    /// Less Than or Equal
    LE,
    /// Always
    AL,
}

impl Condition {
    /// Convert from condition index, to enum value.
    pub fn from_index(idx: i8) -> Option<Condition> {
        if idx < 15 {
            Some(unsafe { mem::transmute(idx) })
        } else {
            None
        }
    }

    /// Convert from enum value to condition index.
    /// This will be a return value between 0 and 0b1110.
    pub fn index(&self) -> i8 {
        *self as i8
    }
}

/// Implement this trait to respond to the emulator.
pub trait ExecutionContext {
    fn undefined(&mut self) {}
    fn unpredictable(&mut self) {}
    
    // Move
    fn mov(&mut self, _flags: InstructionFlags, _dest: Register, _src: ImmOrReg<i32>) { self.undefined() }
    fn adr(&mut self, _dest: Register, _offset: ImmOrReg<i32>) { self.undefined() }

    // Add/subtract
    fn add(&mut self, _flags: InstructionFlags, _dest: Register, _src: ImmOrReg<i32>, _add: ImmOrReg<i32>) { self.undefined() }
    fn sub(&mut self, _flags: InstructionFlags, _dest: Register, _src: ImmOrReg<i32>, _sub: ImmOrReg<i32>) { self.undefined() }
    fn rsb(&mut self, _flags: InstructionFlags, _dest: Register, _src: ImmOrReg<i32>, _sub: ImmOrReg<i32>) { self.undefined() }
    fn adc(&mut self, _flags: InstructionFlags, _dest: Register, _src: ImmOrReg<i32>, _add: ImmOrReg<i32>) { self.undefined() }
    fn sbc(&mut self, _flags: InstructionFlags, _dest: Register, _src: ImmOrReg<i32>, _sub: ImmOrReg<i32>) { self.undefined() }
    fn cmp(&mut self, _flags: InstructionFlags, _a: Register, _b: ImmOrReg<i32>) { self.undefined() }
    fn cmn(&mut self, _flags: InstructionFlags, _a: Register, _b: ImmOrReg<i32>) { self.undefined() }

    // Bitwise
    fn and(&mut self, _flags: InstructionFlags, _dest: Register, _src: ImmOrReg<i32>, _operand: ImmOrReg<i32>) { self.undefined() }
    fn orr(&mut self, _flags: InstructionFlags, _dest: Register, _src: ImmOrReg<i32>, _operand: ImmOrReg<i32>) { self.undefined() }
    fn eor(&mut self, _flags: InstructionFlags, _dest: Register, _src: ImmOrReg<i32>, _operand: ImmOrReg<i32>) { self.undefined() }
    fn lsl(&mut self, _flags: InstructionFlags, _dest: Register, _src: ImmOrReg<i32>, _operand: ImmOrReg<i8>) { self.undefined() }
    fn lsr(&mut self, _flags: InstructionFlags, _dest: Register, _src: ImmOrReg<i32>, _operand: ImmOrReg<i8>) { self.undefined() }
    fn asr(&mut self, _flags: InstructionFlags, _dest: Register, _src: ImmOrReg<i32>, _operand: ImmOrReg<i8>) { self.undefined() }
    fn ror(&mut self, _flags: InstructionFlags, _dest: Register, _src: ImmOrReg<i32>, _operand: ImmOrReg<i8>) { self.undefined() }
    fn rrx(&mut self, _flags: InstructionFlags, _dest: Register, _src: ImmOrReg<i32>) { self.undefined() }
    fn bic(&mut self, _flags: InstructionFlags, _dest: Register, _src: ImmOrReg<i32>, _operand: ImmOrReg<i32>) { self.undefined() }
    fn mvn(&mut self, _flags: InstructionFlags, _dest: Register, _src: ImmOrReg<i32>) { self.undefined() }
    fn test(&mut self, _flags: InstructionFlags, _reg: Register, _src: ImmOrReg<i32>) { self.undefined() }
    fn clz(&mut self, _flags: InstructionFlags, _dest: Register, _rc: Register) { self.undefined() }
    fn teq(&mut self, _flags: InstructionFlags, _dest: Register, _src: i32) { self.undefined() }

    fn mul(&mut self, _flags: InstructionFlags, _dest: Register, _src: ImmOrReg<i32>, _operand: ImmOrReg<i32>) { self.undefined() }
    fn mla(&mut self, _flags: InstructionFlags, _dest: Register, _src: ImmOrReg<i32>, _mul: ImmOrReg<i32>, _add: ImmOrReg<i32>) { self.undefined() }
    fn mls(&mut self, _flags: InstructionFlags, _dest: Register, _src: ImmOrReg<i32>, _mul: ImmOrReg<i32>, _sub: ImmOrReg<i32>) { self.undefined() }
    
    fn b(&mut self, _cond: Condition, _addr: ImmOrReg<i32>, _exchange: bool, _link: bool) { self.undefined() }

    fn str(&mut self, _flags: InstructionFlags, _src: Register, _dest: ImmOrReg<i32>, _off: ImmOrReg<i32>) { self.undefined() }
    fn ldr(&mut self, _flags: InstructionFlags, _dest: Register, _src: ImmOrReg<i32>, _off: ImmOrReg<i32>) { self.undefined() }

    fn cps(&mut self, _interrupt_enable: bool, _primask: bool, _faultmask: bool) { self.undefined() }
    fn cbz(&mut self, _nonzero: bool, _src: Register, _addr: ImmOrReg<i32>) { self.undefined() }
    fn xt(&mut self, _signed: bool, _flags: InstructionFlags, _src: Register, _dest: Register) { self.undefined() }
    fn rev(&mut self, _flags: InstructionFlags, _dest: Register, _src: ImmOrReg<i32>) { self.undefined() }

    fn ldm(&mut self, _flags: InstructionFlags, _dest: Register, _registers: u16, _inc: bool) { self.undefined() }
    fn stm(&mut self, _flags: InstructionFlags, _dest: Register, _registers: u16, _inc: bool) { self.undefined() }

    fn tb(&mut self, _flags: InstructionFlags) { self.undefined() }
    
    fn bkpt(&mut self, _val: i8) { self.undefined() }
    fn it(&mut self, _cond: Condition, _ite: u8, _count: i8) { self.undefined() }
    fn nop(&mut self) {}
    fn yld(&mut self) {}
    fn wfe(&mut self) {}
    fn wfi(&mut self) {}
    fn sev(&mut self) {}
    fn svc(&mut self, _svc: i8) { self.undefined() }

    fn msr(&mut self, _dest: Register, _src: i8) { self.undefined() }
    fn mrs(&mut self, _src: Register, _dest: i8) { self.undefined() }

    fn clrex(&mut self) {}
    fn dsb(&mut self) {}
    fn dmb(&mut self) {}
    fn isb(&mut self) {}
}

/// ARM Emulator error.
#[derive(Copy,Clone,PartialEq,Eq)]
pub enum Error {
    /// Hint for how many more bytes to receive before trying again.
    NotEnoughInput(i8),
    /// Unknown unrecoverable error,
    Unknown,
}

impl error::Error for Error {
    fn description(&self) -> &str {
        match self {
            &Error::NotEnoughInput(_) => "not enough input",
            &Error::Unknown           => "an unknown error occurred",
        }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &Error::NotEnoughInput(x) => write!(fmt, "not enough input (need at least {} more bytes)", x),
            _ => write!(fmt, "{}", error::Error::description(self)),
        }
    }
}

impl fmt::Debug for Error {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(self, fmt)
    }
}

/// ARM emulator error result (for convenience).
pub type Result<T> = result::Result<T, Error>;

pub mod thumb;
pub mod simple;
pub mod disasm;
