use std::{mem, result, error, fmt};

#[macro_use]
extern crate bitflags;

pub type Word = i32;

bitflags! {
    flags InstructionFlags: u16 {
        const INST_NORMAL         = 0,

        const INST_SET_FLAGS      = 1 << 0,
        const INST_HALF           = 1 << 1,
        const INST_BYTE           = 1 << 3,
        const INST_SIGNED         = 1 << 4,
        const INST_WIDE           = 1 << 5,

        // LDM/STM
        const INST_ACQUIRE        = 1 << 6,
        const INST_WRITEBACK      = 1 << 7,
        const INST_DECREMENT      = 1 << 8,
        const INST_BEFORE         = 1 << 9,

        // B
        const INST_LINK           = 1 << 10,
        const INST_EXCHANGE       = 1 << 11,
        const INST_NONZERO        = 1 << 12,

        // PKH
        const INST_TBFORM         = 1 << 9,
    }
}

impl InstructionFlags {
    pub fn get(&self, flag: InstructionFlags) -> bool {
        (*self & flag) != INST_NORMAL
    }
    
    pub fn stack_mode(&self) -> StackMode {
        let dec = (*self & INST_DECREMENT) != INST_NORMAL;
        let before = (*self & INST_BEFORE) != INST_NORMAL;
        match (dec, before) {
            (false, false) => StackMode::IA,
            (false, true)  => StackMode::IB,
            (true, false)  => StackMode::DA,
            (true, true)   => StackMode::DB,
        }
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

#[derive(Copy,Clone,PartialEq,Eq)]
pub enum StoreDoubleMode {
    Offset,
    PostIndex,
    PreIndex,
    Unindexed,
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

/// Shift type (used as an operand to some instructions)
pub enum ShiftType {
    None,
    LSL,
    LSR,
    ASR,
    RRX,
    ROR
}

/// A shift which should be applied to another operand.
pub struct Shift(pub ShiftType, pub ImmOrReg<Word>);

impl Shift {
    pub fn none() -> Shift {
        Shift(ShiftType::None, ImmOrReg::imm(0))
    }
}

/// A shifted operand.
pub struct Shifted(pub Shift, pub ImmOrReg<Word>);

/// LDM/STM modes
pub enum StackMode
{
    IB, // Increment before
    DB, // Decrement before
    IA, // Increment after
    DA, // Decrement after
}

/// Implement this trait to respond to the emulator.
pub trait ExecutionContext {
    fn undefined(&mut self) -> Result<()> { Err(Error::Undefined) }
    fn unpredictable(&mut self) -> Result<()> { Err(Error::Unpredictable) }
    
    // Move
    fn mov(&mut self, _flags: InstructionFlags, _dest: Register, _src: Shifted) -> Result<()> { self.undefined() }
    fn adr(&mut self, _dest: Register, _offset: ImmOrReg<Word>) -> Result<()> { self.undefined() }

    // Add/subtract
    fn add(&mut self, _flags: InstructionFlags, _dest: Register, _src: ImmOrReg<Word>, _add: Shifted) -> Result<()> { self.undefined() }
    fn sub(&mut self, _flags: InstructionFlags, _dest: Register, _src: ImmOrReg<Word>, _sub: Shifted) -> Result<()> { self.undefined() }
    fn rsb(&mut self, _flags: InstructionFlags, _dest: Register, _src: ImmOrReg<Word>, _sub: Shifted) -> Result<()> { self.undefined() }
    fn adc(&mut self, _flags: InstructionFlags, _dest: Register, _src: ImmOrReg<Word>, _add: Shifted) -> Result<()> { self.undefined() }
    fn sbc(&mut self, _flags: InstructionFlags, _dest: Register, _src: ImmOrReg<Word>, _sub: Shifted) -> Result<()> { self.undefined() }
    fn cmp(&mut self, _flags: InstructionFlags, _a: Register, _b: Shifted) -> Result<()> { self.undefined() }
    fn cmn(&mut self, _flags: InstructionFlags, _a: Register, _b: Shifted) -> Result<()> { self.undefined() }

    // Bitwise
    fn and(&mut self, _flags: InstructionFlags, _dest: Register, _src: ImmOrReg<Word>, _operand: Shifted) -> Result<()> { self.undefined() }
    fn orr(&mut self, _flags: InstructionFlags, _dest: Register, _src: ImmOrReg<Word>, _operand: Shifted) -> Result<()> { self.undefined() }
    fn eor(&mut self, _flags: InstructionFlags, _dest: Register, _src: ImmOrReg<Word>, _operand: Shifted) -> Result<()> { self.undefined() }
    fn bic(&mut self, _flags: InstructionFlags, _dest: Register, _src: ImmOrReg<Word>, _operand: Shifted) -> Result<()> { self.undefined() }
    fn mvn(&mut self, _flags: InstructionFlags, _dest: Register, _src: Shifted) -> Result<()> { self.undefined() }
    fn orn(&mut self, _flags: InstructionFlags, _dest: Register, _src: ImmOrReg<Word>, _operand: Shifted) -> Result<()> { self.undefined() }
    fn clz(&mut self, _flags: InstructionFlags, _dest: Register, _rc: Register) -> Result<()> { self.undefined() }
    fn tst(&mut self, _flags: InstructionFlags, _reg: Register, _src: Shifted) -> Result<()> { self.undefined() }
    fn teq(&mut self, _flags: InstructionFlags, _dest: Register, _src: Shifted) -> Result<()> { self.undefined() }

    // Multiplication
    fn mul(&mut self, _flags: InstructionFlags, _dest: Register, _src: ImmOrReg<Word>, _operand: ImmOrReg<Word>) -> Result<()> { self.undefined() }
    fn mla(&mut self, _flags: InstructionFlags, _dest: Register, _src: ImmOrReg<Word>, _mul: ImmOrReg<Word>, _add: ImmOrReg<Word>) -> Result<()> { self.undefined() }
    fn mls(&mut self, _flags: InstructionFlags, _dest: Register, _src: ImmOrReg<Word>, _mul: ImmOrReg<Word>, _sub: ImmOrReg<Word>) -> Result<()> { self.undefined() }

    // Branching
    fn b(&mut self, _flags: InstructionFlags, _cond: Condition, _addr: ImmOrReg<Word>) -> Result<()> { self.undefined() }
    fn cbz(&mut self, _flags: InstructionFlags, _src: Register, _addr: ImmOrReg<Word>) -> Result<()> { self.undefined() }
    fn tb(&mut self, _flags: InstructionFlags, _table: Register, _index: Register) -> Result<()> { self.undefined() }

    // Bytes
    fn xt(&mut self, _flags: InstructionFlags, _src: Register, _dest: Register) -> Result<()> { self.undefined() }
    fn rev(&mut self, _flags: InstructionFlags, _dest: Register, _src: ImmOrReg<Word>) -> Result<()> { self.undefined() }
    fn pkh(&mut self, _flags: InstructionFlags, _dest: Register, _a: Register, _b: Shifted) -> Result<()> { self.undefined() }
    
    // Store/Load
    fn str(&mut self, _flags: InstructionFlags, _src: Register, _dest: ImmOrReg<Word>, _off: ImmOrReg<Word>) -> Result<()> { self.undefined() }
    fn ldr(&mut self, _flags: InstructionFlags, _dest: Register, _src: ImmOrReg<Word>, _off: ImmOrReg<Word>) -> Result<()> { self.undefined() }
    
    fn strex(&mut self, flags: InstructionFlags, res: Register, src: Register,
             dest: ImmOrReg<Word>, off: ImmOrReg<Word>) -> Result<()> {
        try!(self.str(flags, src, dest, off));
        self.mov(INST_NORMAL, res, Shifted(Shift::none(), ImmOrReg::imm(0)))
    }
    fn ldrex(&mut self, flags: InstructionFlags,
             dest: Register, src: ImmOrReg<Word>, off: ImmOrReg<Word>) -> Result<()> { 
        self.ldr(flags, dest, src, off)
    }

    fn strd(&mut self, _flags: InstructionFlags, _mode: StoreDoubleMode,
            _r0: Register, _r1: Register,
            _base: Register, _off: ImmOrReg<Word>) -> Result<()> { self.undefined() }
    fn ldrd(&mut self, _flags: InstructionFlags, _mode: StoreDoubleMode,
            _r0: Register, _r1: Register,
            _base: Register, _off: ImmOrReg<Word>) -> Result<()> { self.undefined() }

    fn strexd(&mut self, _flags: InstructionFlags, _res: Register,
              _r0: Register, _r1: Register, _base: Register) -> Result<()> { self.undefined() }
    fn ldrexd(&mut self, _flags: InstructionFlags,
              _r0: Register, _r1: Register, _base: Register) -> Result<()> { self.undefined() }
    
    fn ldm(&mut self, _flags: InstructionFlags, _addr: Register, _registers: u16) -> Result<()> { self.undefined() }
    fn stm(&mut self, _flags: InstructionFlags, _addr: Register, _registers: u16) -> Result<()> { self.undefined() }
    fn srs(&mut self, _flags: InstructionFlags, _addr: Register, _mode: i8) -> Result<()> { self.undefined() }
    fn rfe(&mut self, _flags: InstructionFlags, _addr: Register) -> Result<()> { self.undefined() }

    // System
    
    fn cps(&mut self, _interrupt_enable: bool, _primask: bool, _faultmask: bool) -> Result<()> { self.undefined() }
    fn bkpt(&mut self, _val: i8) -> Result<()> { self.undefined() }
    fn it(&mut self, _cond: Condition, _ite: u8, _count: i8) -> Result<()> { self.undefined() }
    fn nop(&mut self) -> Result<()> { Ok(()) }
    fn yld(&mut self) -> Result<()> { Ok(()) }
    fn wfe(&mut self) -> Result<()> { Ok(()) }
    fn wfi(&mut self) -> Result<()> { Ok(()) }
    fn sev(&mut self, _local: bool) -> Result<()> { Ok(()) }
    fn svc(&mut self, _svc: i8) -> Result<()> { self.undefined() }
    fn hlt(&mut self, _info: i8) -> Result<()> { self.undefined() }

    fn msr(&mut self, _dest: Register, _src: i8) -> Result<()> { self.undefined() }
    fn mrs(&mut self, _src: Register, _dest: i8) -> Result<()> { self.undefined() }

    fn setend(&mut self, _big_endian: bool) -> Result<()> { self.undefined() }

    fn clrex(&mut self) -> Result<()> { Ok(()) }
    fn dsb(&mut self) -> Result<()> { Ok(()) }
    fn dmb(&mut self) -> Result<()> { Ok(()) }
    fn isb(&mut self) -> Result<()> { Ok(()) }
}

/// ARM Emulator error.
#[derive(Copy,Clone,PartialEq,Eq)]
pub enum Error {
    /// Hint for how many more bytes to receive before trying again.
    NotEnoughInput(i8),
    /// Undefined instruction encountered.
    Undefined,
    /// Unpredictable instruction encountered.
    Unpredictable,
    /// Unknown unrecoverable error.
    Unknown,
}

impl error::Error for Error {
    fn description(&self) -> &str {
        match self {
            &Error::NotEnoughInput(_) => "not enough input",
            &Error::Undefined         => "undefined instruction",
            &Error::Unpredictable     => "unpredictable instruction",
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
