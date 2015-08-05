use std::{mem, result, error, fmt, ops};

#[macro_use]
extern crate bitflags;

pub mod arm;
pub mod thumb;
pub mod simple;
pub mod disasm;

pub trait Int : Copy
    + ops::Sub<Self, Output=Self>
    + ops::BitAnd<Self, Output=Self>
    + ops::Shr<Self, Output=Self>
    + ops::Shl<Self, Output=Self>
    + From<i32>
{
}

impl<T> Int for T where
    T : Copy
    + ops::Sub<T, Output=T>
    + ops::BitAnd<T, Output=T>
    + ops::Shr<T, Output=T>
    + ops::Shl<T, Output=T>
    + From<i32>
{}

pub type Word = i32;

bitflags! {
    flags InstructionFlags: u16 {
        const INST_NORMAL         = 0,

        const INST_SET_FLAGS      = 1 << 0,
        const INST_HALF           = 1 << 1,
        const INST_BYTE           = 1 << 3,
        const INST_SIGNED         = 1 << 4,
        const INST_WIDE           = 1 << 5,
        const INST_TOP            = 1 << 6,
        const INST_BOTTOM         = 1 << 7,

        // LDR/STRd
        const INST_OFFSET         = 1 << 8,
        const INST_POSTINDEX      = 1 << 9,
        const INST_PREINDEX       = 1 << 10,
        const INST_UNPRIV         = 1 << 11,

        // LDM/STM
        const INST_ACQUIRE        = 1 << 11,
        const INST_WRITEBACK      = 1 << 12,
        const INST_DECREMENT      = 1 << 13,
        const INST_BEFORE         = 1 << 14,

        // B
        const INST_LINK           = 1 << 12,
        const INST_EXCHANGE       = 1 << 13,
        const INST_JAZELLE        = 1 << 14,
        const INST_NONZERO        = 1 << 15,

        // PKH
        const INST_TBFORM         = 1 << 11,

        // STC
        const INST_ALT            = 1 << 11,
        const INST_PREINC         = 1 << 12,
        const INST_LONG           = 1 << 13,

        // CPS
        const INST_INTENABLE      = 1 << 1,
        const INST_INTDISABLE     = 1 << 2,
        const INST_CHANGEMODE     = 1 << 3,
        const INST_PSTATEA        = 1 << 4,
        const INST_PSTATEI        = 1 << 5,
        const INST_PSTATEF        = 1 << 6,
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

pub type CP = i8;
pub type CPRegister = i8;

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
    
    fn unpredictable(&mut self) -> Result<()> { Err(Error::Unpredictable) }
    fn undefined(&mut self, msg: &str) -> Result<()> { Err(Error::Undefined(format!("undefined instruction: {}", msg))) }
    fn unimplemented(&mut self, msg: &str) -> Result<()> { Err(Error::Unimplemented(format!("unimplemented instruction: {}", msg))) }
    
    // Move
    fn mov(&mut self, _flags: InstructionFlags, _dest: Register, _src: Shifted) -> Result<()> { self.unimplemented("mov") }

    // Add/subtract
    fn add(&mut self, _flags: InstructionFlags, _dest: Register, _src: ImmOrReg<Word>, _add: Shifted) -> Result<()> { self.unimplemented("add") }
    fn sub(&mut self, _flags: InstructionFlags, _dest: Register, _src: ImmOrReg<Word>, _sub: Shifted) -> Result<()> { self.unimplemented("sub") }
    fn rsb(&mut self, _flags: InstructionFlags, _dest: Register, _src: ImmOrReg<Word>, _sub: Shifted) -> Result<()> { self.unimplemented("rsb") }
    fn adc(&mut self, _flags: InstructionFlags, _dest: Register, _src: ImmOrReg<Word>, _add: Shifted) -> Result<()> { self.unimplemented("adc") }
    fn sbc(&mut self, _flags: InstructionFlags, _dest: Register, _src: ImmOrReg<Word>, _sub: Shifted) -> Result<()> { self.unimplemented("sbc") }
    fn cmp(&mut self, _flags: InstructionFlags, _a: Register, _b: Shifted) -> Result<()> { self.unimplemented("cmp") }
    fn cmn(&mut self, _flags: InstructionFlags, _a: Register, _b: Shifted) -> Result<()> { self.unimplemented("cmn") }

    // Bitwise
    fn and(&mut self, _flags: InstructionFlags, _dest: Register, _src: ImmOrReg<Word>, _operand: Shifted) -> Result<()> { self.unimplemented("and") }
    fn orr(&mut self, _flags: InstructionFlags, _dest: Register, _src: ImmOrReg<Word>, _operand: Shifted) -> Result<()> { self.unimplemented("orr") }
    fn eor(&mut self, _flags: InstructionFlags, _dest: Register, _src: ImmOrReg<Word>, _operand: Shifted) -> Result<()> { self.unimplemented("eor") }
    fn bic(&mut self, _flags: InstructionFlags, _dest: Register, _src: ImmOrReg<Word>, _operand: Shifted) -> Result<()> { self.unimplemented("bic") }
    fn mvn(&mut self, _flags: InstructionFlags, _dest: Register, _src: Shifted) -> Result<()> { self.unimplemented("mvn") }
    fn orn(&mut self, _flags: InstructionFlags, _dest: Register, _src: ImmOrReg<Word>, _operand: Shifted) -> Result<()> { self.unimplemented("orn") }
    fn clz(&mut self, _flags: InstructionFlags, _dest: Register, _rc: Register) -> Result<()> { self.unimplemented("clz") }
    fn tst(&mut self, _flags: InstructionFlags, _reg: Register, _src: Shifted) -> Result<()> { self.unimplemented("tst") }
    fn teq(&mut self, _flags: InstructionFlags, _dest: Register, _src: Shifted) -> Result<()> { self.unimplemented("teq") }

    // Multiplication
    fn mul(&mut self, _flags: InstructionFlags, _dest: Register, _src: ImmOrReg<Word>, _operand: ImmOrReg<Word>) -> Result<()> { self.unimplemented("mul") }
    fn mla(&mut self, _flags: InstructionFlags, _dest: Register, _src: ImmOrReg<Word>, _mul: ImmOrReg<Word>, _add: ImmOrReg<Word>) -> Result<()> { self.unimplemented("mla") }
    fn mls(&mut self, _flags: InstructionFlags, _dest: Register, _src: ImmOrReg<Word>, _mul: ImmOrReg<Word>, _sub: ImmOrReg<Word>) -> Result<()> { self.unimplemented("mls") }

    // Branching
    fn b(&mut self, _flags: InstructionFlags, _cond: Condition, _base: Register, _off: ImmOrReg<Word>) -> Result<()> { self.unimplemented("b") }
    fn cbz(&mut self, _flags: InstructionFlags, _src: Register, _base: Register, _off: ImmOrReg<Word>) -> Result<()> { self.unimplemented("cbz") }
    fn tb(&mut self, _flags: InstructionFlags, _table: Register, _index: Register) -> Result<()> { self.unimplemented("tb") }
    fn eret(&mut self) -> Result<()> { self.unimplemented("eret") }

    // Bytes
    fn xt(&mut self, _flags: InstructionFlags, _src: Register, _dest: Register) -> Result<()> { self.unimplemented("xt") }
    fn rev(&mut self, _flags: InstructionFlags, _dest: Register, _src: ImmOrReg<Word>) -> Result<()> { self.unimplemented("rev") }
    fn pkh(&mut self, _flags: InstructionFlags, _dest: Register, _a: Register, _b: Shifted) -> Result<()> { self.unimplemented("pkh") }
    
    // Store/Load
    fn str(&mut self, _flags: InstructionFlags, _src: Register, _dest: ImmOrReg<Word>, _off: Shifted) -> Result<()> { self.unimplemented("str") }
    fn ldr(&mut self, _flags: InstructionFlags, _dest: Register, _src: ImmOrReg<Word>, _off: Shifted) -> Result<()> { self.unimplemented("ldr") }
    
    fn strex(&mut self, flags: InstructionFlags, res: Register, src: Register,
             dest: ImmOrReg<Word>, off: Shifted) -> Result<()> {
        try!(self.str(flags, src, dest, off));
        self.mov(INST_NORMAL, res, Shifted(Shift::none(), ImmOrReg::imm(0)))
    }
    fn ldrex(&mut self, flags: InstructionFlags,
             dest: Register, src: ImmOrReg<Word>, off: Shifted) -> Result<()> { 
        self.ldr(flags, dest, src, off)
    }

    fn strd(&mut self, _flags: InstructionFlags,
            _r0: Register, _r1: Register,
            _base: Register, _off: ImmOrReg<Word>) -> Result<()> { self.unimplemented("strd") }
    fn ldrd(&mut self, _flags: InstructionFlags,
            _r0: Register, _r1: Register,
            _base: Register, _off: ImmOrReg<Word>) -> Result<()> { self.unimplemented("ldrd") }

    fn strexd(&mut self, _flags: InstructionFlags, _res: Register,
              _r0: Register, _r1: Register, _base: Register) -> Result<()> { self.unimplemented("strexd") }
    fn ldrexd(&mut self, _flags: InstructionFlags,
              _r0: Register, _r1: Register, _base: Register) -> Result<()> { self.unimplemented("ldrexd") }
    
    fn ldm(&mut self, _flags: InstructionFlags, _addr: Register, _registers: u16) -> Result<()> { self.unimplemented("ldm") }
    fn stm(&mut self, _flags: InstructionFlags, _addr: Register, _registers: u16) -> Result<()> { self.unimplemented("stm") }
    fn srs(&mut self, _flags: InstructionFlags, _addr: Register, _mode: i8) -> Result<()> { self.unimplemented("srs") }
    fn rfe(&mut self, _flags: InstructionFlags, _addr: Register) -> Result<()> { self.unimplemented("rfe") }

    // System
    
    fn cps(&mut self, _flags: InstructionFlags, _mode: i8) -> Result<()> { self.unimplemented("cps") }
    fn bkpt(&mut self, _val: i8) -> Result<()> { self.unimplemented("bkpt") }
    fn it(&mut self, _cond: Condition, _ite: u8, _count: i8) -> Result<()> { self.unimplemented("it") }
    fn nop(&mut self) -> Result<()> { Ok(()) }
    fn yld(&mut self) -> Result<()> { Ok(()) }
    fn wfe(&mut self) -> Result<()> { Ok(()) }
    fn wfi(&mut self) -> Result<()> { Ok(()) }
    fn sev(&mut self, _local: bool) -> Result<()> { Ok(()) }
    fn svc(&mut self, _svc: i8) -> Result<()> { self.unimplemented("svc") }
    fn hlt(&mut self, _info: i8) -> Result<()> { self.unimplemented("hlt") }
    fn dbg(&mut self, _info: i8) -> Result<()> { self.unimplemented("dbg") }
    fn hvc(&mut self, _call: i16) -> Result<()> { self.unimplemented("hvc") }
    fn smc(&mut self, _call: i8) -> Result<()> { self.unimplemented("smc") }

    fn msr(&mut self, _flags: InstructionFlags, _src: Register, _dest: i8, _mask: i8) -> Result<()> { self.unimplemented("msr") }
    fn mrs(&mut self, _flags: InstructionFlags, _dest: Register, _src: i8) -> Result<()> { self.unimplemented("mrs") }

    fn setend(&mut self, _big_endian: bool) -> Result<()> { self.unimplemented("setend") }

    fn clrex(&mut self) -> Result<()> { Ok(()) }
    fn dsb(&mut self) -> Result<()> { Ok(()) }
    fn dmb(&mut self) -> Result<()> { Ok(()) }
    fn isb(&mut self) -> Result<()> { Ok(()) }

    // Coprocessor

    fn stc(&mut self, _flags: InstructionFlags, _coproc: CP, _reg: CPRegister,
           _base: Register, _offset: ImmOrReg<Word>, _option: u8) -> Result<()> { self.unimplemented("stc") }
    fn ldc(&mut self, _flags: InstructionFlags, _coproc: CP, _reg: CPRegister,
           _base: Register, _offset: ImmOrReg<Word>, _option: u8) -> Result<()> { self.unimplemented("ldc") }
    fn mcr(&mut self, _flags: InstructionFlags, _coproc: CP, _target: Register,
           _r0: CPRegister, _opcode0: i8,
           _r1: CPRegister, _opcode1: i8) -> Result<()> { self.unimplemented("mcr") }
    fn mrc(&mut self, _flags: InstructionFlags, _coproc: CP, _target: Register,
           _r0: CPRegister, _opcode0: i8,
           _r1: CPRegister, _opcode1: i8) -> Result<()> { self.unimplemented("mrc") }
    fn mcrr(&mut self, _flags: InstructionFlags, _coproc: CP, _opcode: i8, _reg: CPRegister,
            _r0: Register, _r1: Register) -> Result<()> { self.unimplemented("mcrr") }
    fn mrrc(&mut self, _flags: InstructionFlags, _coproc: CP, _opcode: i8, _reg: CPRegister,
            _r0: Register, _r1: Register) -> Result<()> { self.unimplemented("mrrc") }
    fn cdp(&mut self, _flags: InstructionFlags, _coproc: CP, _dest: CPRegister,
           _opcode0: i8, _r0: CPRegister, _opcode1: i8, _r1: CPRegister) -> Result<()> { self.unimplemented("cdp") }
}

/// ARM Emulator error.
#[derive(Clone,PartialEq,Eq)]
pub enum Error {
    /// Hint for how many more bytes to receive before trying again.
    NotEnoughInput(i8),
    /// Undefined instruction encountered.
    Undefined(String),
    /// Unpredictable instruction encountered.
    Unpredictable,
    /// Unimplemented codepath.
    Unimplemented(String),
    /// Unknown unrecoverable error.
    Unknown,
}

impl error::Error for Error {
    fn description(&self) -> &str {
        match self {
            &Error::NotEnoughInput(_)    => "not enough input",
            &Error::Undefined(ref x)     => &x,
            &Error::Unpredictable        => "unpredictable instruction",
            &Error::Unknown              => "an unknown error occurred",
            &Error::Unimplemented(ref x) => &x,
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

fn extend_signed<T: Int>(src: T, bits: T) -> T {
    let src_bits = T::from(mem::size_of::<T>() as i32);
    let shift_amt = src_bits - bits;

    // Left-pad with sign bit
    (src << shift_amt) >> shift_amt
}
