// Parser for the THUMB-2 instruction set

use std::fmt;
use std::ops;

use super::*;
use super::{register, condition};
use super::disasm::Disassembler;

#[inline]
/// Extract bits from a source integer.
fn bits<T>(src: T, start: T, count: T) -> T
    where T: ops::Sub<T, Output=T> + ops::BitAnd<T, Output=T>
    + ops::Shr<T, Output=T> + ops::Shl<T, Output=T> + From<i32>
{
    (src >> start) & ((T::from(1) << count)-T::from(1))
}

#[inline]
/// Decode the immediate shift operand into a Shift struct.
/// (Which can be used later to shift calculated values.)
fn decode_imm_shift(op: Word, imm: Word) -> Shift {
    match op {
        0b00 => Shift(ShiftType::LSL, ImmOrReg::imm(imm)),
        0b01 => Shift(ShiftType::LSR, ImmOrReg::imm(if imm == 0 { 32 } else { imm })),
        0b10 => Shift(ShiftType::ASR, ImmOrReg::imm(if imm == 0 { 32 } else { imm })),
        0b11 => if imm == 0 {
            Shift(ShiftType::RRX, ImmOrReg::imm(1))
        } else {
            Shift(ShiftType::ROR, ImmOrReg::imm(imm))
        },
        _ => panic!("invalid imm shift"),
    }
}

#[inline]
fn decode_reg_shift(op: Word, reg: Register) -> Shift {
    match op {
        0b0010 => Shift(ShiftType::LSL, ImmOrReg::Reg(reg)),
        0b0011 => Shift(ShiftType::LSR, ImmOrReg::Reg(reg)),
        0b0100 => Shift(ShiftType::ASR, ImmOrReg::Reg(reg)),
        0b0111 => Shift(ShiftType::ROR, ImmOrReg::Reg(reg)),
        _ => panic!("invalid reg shift"),
    }
}

/// Execute up to one THUMB instruction.
pub fn execute<'a, 'b, T : ExecutionContext>(context: &'b mut T, mut buffer: &'a [u8]) -> (&'a [u8], Result<()>) {
    if buffer.len() < 2  {
        return (buffer, Err(Error::NotEnoughInput(2)))
    }

    // Check whether we've got a 32-bit instruction
    let is_16bit = ((buffer[0] & 0xe0) != 0xe0)
        || ((buffer[0] & 0x18) == 0);

    // If so, check we have enough bytes
    if !is_16bit && (buffer.len() < 4) {
        return (buffer, Err(Error::NotEnoughInput(4)))
    }

    if is_16bit {
        match execute_16((buffer[1] as u16)
                         | ((buffer[0] as u16) << 8),
                         context) {
            Err(x) => return (buffer, Err(x)),
            _ => buffer = &buffer[2..],
        }
        
    } else {
        match execute_32(buffer[3] as u32
                         | ((buffer[2] as u32) << 8)
                         | ((buffer[1] as u32) << 16)
                         | ((buffer[0] as u32) << 24),
                         context) {
            Err(x) => return (buffer, Err(x)),
            _ => buffer = &buffer[4..],
        }
    }

    (buffer, Ok(()))
}

/// Disassemble some THUMB code.
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

/// Execute a thumb-16 instruction as an integer.
pub fn execute_16<T: ExecutionContext>(src: u16, context: &mut T) -> Result<()> {
    match src {

        //
        // F3.2.1 - Shift (imm), add, subtract, move and compare
        //
        
        0b0000_000000000000...0b0000_111111111111 |
        0b00010_00000000000...0b00010_11111111111 =>
            context.mov(INST_SET_FLAGS,
                        register((src & 7) as i8),
                        ImmOrReg::register(((src >> 3) & 7) as i8),
                        decode_imm_shift(bits(src as i32, 11, 2), bits(src as i32, 6, 5))),

        0b0001100_000000000...0b0001100_111111111 =>
            context.add(INST_SET_FLAGS,
                        register((src & 7) as i8),
                        ImmOrReg::register(((src >> 3) & 7) as i8),
                        ImmOrReg::imm(((src >> 6) & 7) as i32)),

        0b0001101_000000000...0b0001101_111111111 =>
            context.sub(INST_SET_FLAGS,
                        register((src & 7) as i8),
                        ImmOrReg::register(((src >> 3) & 7) as i8),
                        ImmOrReg::register(((src >> 6) & 7) as i8)),
        
        0b0001110_000000000...0b0001110_111111111 =>
            context.add(INST_SET_FLAGS,
                        register((src & 7) as i8),
                        ImmOrReg::register(((src >> 3) & 7) as i8),
                        ImmOrReg::imm(((src >> 6) & 7) as i32)),
            
        0b0001111_000000000...0b0001111_111111111 =>
            context.sub(INST_SET_FLAGS,
                        register((src & 7) as i8),
                        ImmOrReg::register(((src >> 3) & 7) as i8),
                        ImmOrReg::imm(((src >> 6) & 7) as i32)),
        
        0b00100_00000000000...0b00100_11111111111 =>
            context.mov(INST_SET_FLAGS,
                        register(((src >> 8) & 7) as i8),
                        ImmOrReg::imm((src & 0xff) as i32),
                        Shift::none()),
        
        0b00101_00000000000...0b00101_11111111111 =>
            context.cmp(INST_NORMAL,
                        register(((src >> 8) & 7) as i8),
                        ImmOrReg::imm((src & 0xff) as i32)),
        
        0b00110_00000000000...0b00110_11111111111 =>
            context.add(INST_SET_FLAGS,
                        register(((src >> 8) & 7) as i8),
                        ImmOrReg::register(((src >> 8) & 7) as i8),
                        ImmOrReg::imm((src & 0xff) as i32)),
        
        0b00111_00000000000...0b00111_11111111111 =>
            context.sub(INST_SET_FLAGS,
                        register(((src >> 8) & 7) as i8),
                        ImmOrReg::register(((src >> 8) & 7) as i8),
                        ImmOrReg::imm((src & 0xff) as i32)),

        //
        // F3.2.2 Data-Processing
        //
        
        0b0100000000_000000...0b0100000000_111111 =>
            context.and(INST_SET_FLAGS,
                        register((src & 7) as i8),
                        ImmOrReg::register((src & 7) as i8),
                        ImmOrReg::register(((src >> 3) & 7) as i8)),
        
        0b0100000001_000000...0b0100000001_111111 =>
            context.eor(INST_SET_FLAGS,
                        register((src & 7) as i8),
                        ImmOrReg::register((src & 7) as i8),
                        ImmOrReg::register(((src >> 3) & 7) as i8)),

        0b010000001_0000000...0b010000001_1111111 |
        0b0100000100_000000...0b0100000100_111111 |
        0b0100000111_000000...0b0100000111_111111 =>
            context.mov(INST_SET_FLAGS,
                        register((src & 7) as i8),
                        ImmOrReg::register((src & 7) as i8),
                        decode_reg_shift(bits(src as i32, 6, 4), register(bits(src as i32, 3, 3) as i8))),

        0b0100000101_000000...0b0100000101_111111 =>
            context.adc(INST_SET_FLAGS,
                        register((src & 7) as i8),
                        ImmOrReg::register((src & 7) as i8),
                        ImmOrReg::register(((src >> 3) & 7) as i8)),
        
        0b0100000110_000000...0b0100000110_111111 =>
            context.sbc(INST_SET_FLAGS,
                        register((src & 7) as i8),
                        ImmOrReg::register((src & 7) as i8),
                        ImmOrReg::register(((src >> 3) & 7) as i8)),
        
        0b0100001000_000000...0b0100001000_111111 =>
            context.test(INST_NORMAL,
                         register((src & 7) as i8),
                         ImmOrReg::register(((src >> 3) & 7) as i8)),
        
        0b0100001001_000000...0b0100001001_111111 =>
            context.rsb(INST_SET_FLAGS,
                        register((src & 7) as i8),
                        ImmOrReg::register(((src >> 3) & 7) as i8),
                        ImmOrReg::imm(0)),
        
        0b0100001010_000000...0b0100001010_111111 =>
            context.cmp(INST_NORMAL,
                        register((src & 7) as i8),
                        ImmOrReg::register(((src >> 3) & 7) as i8)),
        
        0b0100001011_000000...0b0100001011_111111 =>
            context.cmn(INST_NORMAL,
                        register((src & 7) as i8),
                        ImmOrReg::register(((src >> 3) & 7) as i8)),
        
        0b0100001100_000000...0b0100001100_111111 =>
            context.orr(INST_SET_FLAGS,
                        register((src & 7) as i8),
                        ImmOrReg::register((src & 7) as i8),
                        ImmOrReg::register(((src >> 3) & 7) as i8)),
        
        0b0100001101_000000...0b0100001101_111111 =>
            context.mul(INST_SET_FLAGS,
                        register((src & 7) as i8),
                        ImmOrReg::register((src & 7) as i8),
                        ImmOrReg::register(((src >> 3) & 7) as i8)),
        
        0b0100001110_000000...0b0100001110_111111 =>
            context.bic(INST_SET_FLAGS,
                        register((src & 7) as i8),
                        ImmOrReg::register((src & 7) as i8),
                        ImmOrReg::register(((src >> 3) & 7) as i8)),
        
        0b0100001111_000000...0b0100001111_111111 =>
            context.mvn(INST_SET_FLAGS,
                        register((src & 7) as i8),
                        ImmOrReg::register(((src >> 3) & 7) as i8)),

        //
        // F3.2.3 - Special data instruction and branch and exchange
        //

        0b01000100_00000000...0b01000100_11111111 => {
            let rdn = register(((src & 7) | ((src >> 4) & 0x80)) as i8);
            context.add(INST_SET_FLAGS,
                        rdn,
                        ImmOrReg::Reg(rdn),
                        ImmOrReg::register(((src >> 3) & 0xf) as i8))
        },

        0b01000101_00000000...0b01000101_11111111 =>
            context.cmp(INST_NORMAL,
                        register(((src & 7) | ((src >> 4) & 0x80)) as i8),
                        ImmOrReg::register(((src >> 3) & 0xf) as i8)),

        0b01000110_00000000...0b01000110_11111111 =>
            context.mov(INST_NORMAL,
                        register(((src & 7) | ((src >> 4) & 0x80)) as i8),
                        ImmOrReg::register(((src >> 3) & 0xf) as i8),
                        Shift::none()),

        0b010001110_0000000...0b010001110_1111111 =>
            context.b(INST_EXCHANGE,
                      Condition::AL,
                      ImmOrReg::register(((src >> 3) & 0xf) as i8)),
        
        0b010001111_0000000...0b010001111_1111111 =>
            context.b(INST_LINK | INST_EXCHANGE,
                      Condition::AL,
                      ImmOrReg::register(((src >> 3) & 0xf) as i8)),

        //
        // Load Literal
        //

        0b01001_00000000000...0b01001_11111111111 =>
            context.ldr(INST_NORMAL,
                        register(((src >> 8) & 7) as i8),
                        ImmOrReg::Reg(Register::PC),
                        ImmOrReg::imm(((src & 0xf) as i32) << 2)),

        //
        // Load/Store single data item
        //

        0b0101000_000000000...0b0101000_111111111 =>
            context.str(INST_NORMAL,
                        register((src & 7) as i8),
                        ImmOrReg::register(((src >> 3) & 7) as i8),
                        ImmOrReg::register(((src >> 6) & 7) as i8)),
        
        0b0101001_000000000...0b0101001_111111111 =>
            context.str(INST_HALF,
                        register((src & 7) as i8),
                        ImmOrReg::register(((src >> 3) & 7) as i8),
                        ImmOrReg::register(((src >> 6) & 7) as i8)),
        
        0b0101010_000000000...0b0101010_111111111 =>
            context.str(INST_HALF,
                        register((src & 7) as i8),
                        ImmOrReg::register(((src >> 3) & 7) as i8),
                        ImmOrReg::register(((src >> 6) & 7) as i8)),
        
        0b0101011_000000000...0b0101011_111111111 =>
            context.ldr(INST_BYTE | INST_SIGNED,
                        register((src & 7) as i8),
                        ImmOrReg::register(((src >> 3) & 7) as i8),
                        ImmOrReg::register(((src >> 6) & 7) as i8)),
        
        0b0101100_000000000...0b0101100_111111111 =>
            context.ldr(INST_NORMAL,
                        register((src & 7) as i8),
                        ImmOrReg::register(((src >> 3) & 7) as i8),
                        ImmOrReg::register(((src >> 6) & 7) as i8)),
        
        0b0101101_000000000...0b0101101_111111111 =>
            context.ldr(INST_HALF,
                        register((src & 7) as i8),
                        ImmOrReg::register(((src >> 3) & 7) as i8),
                        ImmOrReg::register(((src >> 6) & 7) as i8)),
        
        0b0101110_000000000...0b0101110_111111111 =>
            context.ldr(INST_BYTE,
                        register((src & 7) as i8),
                        ImmOrReg::register(((src >> 3) & 7) as i8),
                        ImmOrReg::register(((src >> 6) & 7) as i8)),
        
        0b0101111_000000000...0b0101111_111111111 =>
            context.ldr(INST_HALF | INST_SIGNED,
                        register((src & 7) as i8),
                        ImmOrReg::register(((src >> 3) & 7) as i8),
                        ImmOrReg::register(((src >> 6) & 7) as i8)),

        0b01100_00000000000...0b01100_11111111111 =>
            context.str(INST_NORMAL,
                        register((src & 7) as i8),
                        ImmOrReg::register(((src >> 3) & 7) as i8),
                        ImmOrReg::imm(((src >> 6) & 0x1f) as i32)),

        0b01101_00000000000...0b01101_11111111111 =>
            context.ldr(INST_NORMAL,
                        register((src & 7) as i8),
                        ImmOrReg::register(((src >> 3) & 7) as i8),
                        ImmOrReg::imm(((src >> 6) & 0x1f) as i32)),

        0b01110_00000000000...0b01110_11111111111 =>
            context.str(INST_BYTE,
                        register((src & 7) as i8),
                        ImmOrReg::register(((src >> 3) & 7) as i8),
                        ImmOrReg::imm(((src >> 6) & 0x1f) as i32)),
        

        0b01111_00000000000...0b01111_11111111111 =>
            context.ldr(INST_BYTE,
                        register((src & 7) as i8),
                        ImmOrReg::register(((src >> 3) & 7) as i8),
                        ImmOrReg::imm(((src >> 6) & 0x1f) as i32)),

        0b10000_00000000000...0b10000_11111111111 =>
            context.str(INST_HALF,
                        register((src & 7) as i8),
                        ImmOrReg::register(((src >> 3) & 7) as i8),
                        ImmOrReg::imm(((src >> 6) & 0x1f) as i32)),
        

        0b10001_00000000000...0b10001_11111111111 =>
            context.ldr(INST_HALF,
                        register((src & 7) as i8),
                        ImmOrReg::register(((src >> 3) & 7) as i8),
                        ImmOrReg::imm(((src >> 6) & 0x1f) as i32)),

        0b10010_00000000000...0b10010_11111111111 =>
            context.str(INST_NORMAL,
                        register(((src >> 8) & 7) as i8),
                        ImmOrReg::Reg(Register::SP),
                        ImmOrReg::imm((src & 0xff) as i32)),
        

        0b10011_00000000000...0b10011_11111111111 =>
            context.ldr(INST_NORMAL,
                        register(((src >> 8) & 7) as i8),
                        ImmOrReg::Reg(Register::SP),
                        ImmOrReg::imm((src & 0xff) as i32)),

        // ADR
        0b10100_00000000000...0b10100_11111111111 =>
            context.adr(register(((src >> 8) & 0x7) as i8),
                        ImmOrReg::imm((src & 0xff) as i32)),
        
        // ADD (SP+imm)
        0b10101_00000000000...0b10101_11111111111 =>
            context.add(INST_NORMAL,
                        register(((src >> 8) & 7) as i8),
                        ImmOrReg::Reg(Register::SP),
                        ImmOrReg::imm((src & 0xff) as i32)),

        //
        // F3.2.5 - Miscellaneous 16-bit instructions
        //

        0b101100000_0000000...0b101100000_1111111 =>
            context.add(INST_NORMAL,
                        Register::SP,
                        ImmOrReg::Reg(Register::SP),
                        ImmOrReg::imm((src & 0x7f) as i32)),
        
        0b101100001_0000000...0b101100001_1111111 =>
            context.sub(INST_NORMAL,
                        Register::SP,
                        ImmOrReg::Reg(Register::SP),
                        ImmOrReg::imm((src & 0x7f) as i32)),
        
        0b10110001_00000000...0b10110001_11111111 =>
            context.cbz(INST_NORMAL,
                        register((src & 3) as i8),
                        ImmOrReg::imm(((src >> 2) & 0x3e) as i32)),

        0b1011001000_000000...0b1011001000_111111 =>
            context.xt(INST_HALF | INST_SIGNED,
                       register((src & 7) as i8),
                       register(((src >> 3) & 7) as i8)),
        
        0b1011001001_000000...0b1011001001_111111 =>
            context.xt(INST_BYTE | INST_SIGNED,
                       register((src & 7) as i8),
                       register(((src >> 3) & 7) as i8)),

        0b10110010100_00000...0b10110010100_11111 =>
            context.xt(INST_HALF,
                       register((src & 7) as i8),
                       register(((src >> 3) & 7) as i8)),
        
        0b10110010110_00000...0b10110010110_11111 =>
            context.xt(INST_BYTE,
                       register((src & 7) as i8),
                       register(((src >> 3) & 7) as i8)),

        0b10110011_00000000...0b10110011_11111111 =>
            context.cbz(INST_NORMAL,
                        register((src & 3) as i8),
                        ImmOrReg::imm((((src >> 2) & 0x3e) | 0x40) as i32)),
        
        0b1011010_000000000...0b1011010_111111111 =>
            context.stm(INST_WRITEBACK,
                        Register::SP,
                        (0x4000 | (src & 0xff)) as u16),

        0b10110110010_00000...0b10110110010_11111 =>
            context.setend(bits(src as i32, 3, 1) != 0),
        
        0b10110110011_00000...0b10110110011_11111 =>
            context.cps((src & 0x10) != 0,
                        (src & 0x02) != 0,
                        (src & 0x01) != 0),

        0b10111001_00000000...0b10111001_11111111 =>
            context.cbz(INST_NONZERO,
                        register((src & 3) as i8),
                        ImmOrReg::imm(((src >> 2) & 0x3e) as i32)),
        
        0b1011101000_000000...0b1011101000_111111 =>
            context.rev(INST_NORMAL,
                        register((src & 7) as i8),
                        ImmOrReg::register(((src >> 3) & 7) as i8)),

        0b1011101001_000000...0b1011101001_111111 =>
            context.rev(INST_HALF,
                        register((src & 7) as i8),
                        ImmOrReg::register(((src >> 3) & 7) as i8)),
        
        0b1011101010_000000...0b1011101010_111111 =>
            context.hlt((src & 0x3f) as i8),

        0b1011101011_000000...0b1011101011_111111 =>
            context.rev(INST_HALF | INST_SIGNED,
                        register((src & 7) as i8),
                        ImmOrReg::register(((src >> 3) & 7) as i8)),
        
        0b10111011_00000000...0b10111011_11111111 =>
            context.cbz(INST_NONZERO,
                        register((src & 3) as i8),
                        ImmOrReg::imm(((src >> 2) & 0x3e) as i32)),
        
        0b1011110_000000000...0b1011110_111111111 =>
            context.ldm(INST_WRITEBACK,
                        Register::SP,
                        (0x4000 | (src & 0xff)) as u16),

        0b10111110_00000000...0b10111110_11111111 =>
            context.bkpt((src & 0xff) as i8),

        0b10111111_00000000...0b10111111_11111111 =>
            if (src & 0xf) != 0 {
                // IT
                
                let cond = ((src >> 4) & 0xf) as i8;
                let mask = src & 0xf;
                let bit = if (cond & 1) != 0 { 0u16 } else { 0xffffu16 };
                let mut count = 0;
                
                if (mask & 1) != 0 {
                    count = 3
                } else if (mask & 2) != 0 {
                    count = 2
                } else if (mask & 4) != 0 {
                    count = 1
                } else if (mask & 8) == 0 {
                    panic!("bad parse in thumb 16-bit ITT")
                }
                
                context.it(condition(cond), (mask ^ bit) as u8, count)
            } else {
                match (src >> 4) & 0xf {
                    0b0000 => context.nop(),
                    0b0001 => context.yld(),
                    0b0010 => context.wfe(),
                    0b0011 => context.wfi(),
                    0b0100 => context.sev(false),
                    0b0101 => context.sev(true),
                    
                    _ => context.nop(),
                }
            },
        
        // STM
        0b11000_00000000000...0b11000_11111111111 =>
            context.stm(INST_WRITEBACK,
                        register(((src >> 8) & 7) as i8),
                        (src & 0xff) as u16),

        // LDM
        0b11001_00000000000...0b11001_11111111111 => {
            let reg_idx = (src >> 8) & 7;
            context.ldm(if (src & (1 << reg_idx)) != 0 { INST_WRITEBACK } else { INST_NORMAL},
                        register(reg_idx as i8),
                        (src & 0xff) as u16)
        },

        0b11011110_00000000...0b11011110_11111111 => context.undefined(),
        0b11011111_00000000...0b11011111_11111111 => context.svc((src & 0xff) as i8),

        0b1101_000000000000...0b1101_111111111111  =>
            context.b(INST_NORMAL,
                      condition(((src >> 8) & 0xf) as i8),
                      ImmOrReg::imm(((src & 0xff) << 1) as i32)),
            
        0b11100_00000000000...0b11100_11111111111 =>
            context.b(INST_NORMAL,
                      Condition::AL,
                      ImmOrReg::imm((((src & 0x3ff) << 2) as i32) >> 1)),
        
        _ => context.undefined(),
    }
}

/// Execute a THUMB-32 instruction as an integer.
pub fn execute_32<T: ExecutionContext>(src: u32, context: &mut T) -> Result<()> {
    match src {
        0...0b11100_11111111111_1111111111111111 => panic!("invalid 32-bit thumb instruction"),
        
        0b1110100010_000000_0000000000000000...0b1110100010_111111_1111111111111111 |
        0b1110100100_000000_0000000000000000...0b1110100100_111111_1111111111111111 => {
            let load = ((src >> 20) & 1) != 0;
            let reg = register(bits(src as i32, 16, 4) as i8);
            let regs = (src & 0xffff) as u16;
            
            let flags = if ((src >> 21) & 1) == 1 {
                INST_WRITEBACK
            } else {
                INST_NORMAL
            };

            let flags = if ((src >> 24) & 1) == 1 {
                INST_DECREMENT | INST_BEFORE | flags
            } else {
                INST_NORMAL | flags
            };
            
            if load {
                context.ldm(flags, reg, regs)
            } else {
                context.stm(flags, reg, regs)
            }
        },

        0b1110100000_000000_0000000000000000...0b1110100000_111111_1111111111111111 |
        0b1110100110_000000_0000000000000000...0b1110100110_111111_1111111111111111 => {
            let load = ((src >> 20) & 1) != 0;
            let reg = register(bits(src as i32, 16, 4) as i8);
            
            let flags = if ((src >> 21) & 1) == 1 {
                INST_WRITEBACK
            } else {
                INST_NORMAL
            };
                
            let flags = if ((src >> 23) & 1) == 0 {
                INST_DECREMENT | INST_BEFORE | flags
            } else {
                INST_NORMAL | flags
            };

            if load {
                context.rfe(flags, reg)
            } else {
                context.srs(flags, reg, bits(src as i32, 0, 5) as i8)
            }
        },

        // STREX
        0b111010000100_0000_0000000000000000...0b111010000100_1111_1111111111111111 =>
            context.strex(INST_NORMAL,
                          register(bits(src as i32, 8, 4) as i8),
                          register(bits(src as i32, 12, 4) as i8),
                          ImmOrReg::register(bits(src as i32, 16, 4) as i8),
                          ImmOrReg::imm(bits(src as i32, 0, 8))),
        // LDREX
        0b111010000101_0000_0000000000000000...0b111010000101_1111_1111111111111111 =>
            context.ldrex(INST_NORMAL,
                          register(bits(src as i32, 12, 4) as i8),
                          ImmOrReg::register(bits(src as i32, 16, 4) as i8),
                          ImmOrReg::imm(bits(src as i32, 0, 8))),

        // STRD
        0b111010000110_0000_0000000000000000...0b111010000110_1111_1111111111111111 |
        0b111010001110_0000_0000000000000000...0b111010001110_1111_1111111111111111 |
        0b111010010100_0000_0000000000000000...0b111010010100_1111_1111111111111111 |
        0b111010011100_0000_0000000000000000...0b111010011100_1111_1111111111111111 |
        0b111010010110_0000_0000000000000000...0b111010010110_1111_1111111111111111 |
        0b111010011110_0000_0000000000000000...0b111010011110_1111_1111111111111111 => {
            let mode = match (((src >> 23) & 1) != 0, ((src >> 21) & 1) != 0) { // PW
                (true, false) => StoreDoubleMode::Offset,
                (false, true) => StoreDoubleMode::PostIndex,
                (true, true)  => StoreDoubleMode::PreIndex,
                _ => return context.unpredictable(),
            };
            
            let neg = ((src >> 24) & 1) != 0;
            let val = bits(src as i32, 0, 8);
            let val = if neg { -val } else { val };

            context.strd(INST_NORMAL, mode,
                         register(bits(src as i32, 12, 4) as i8),
                         register(bits(src as i32, 8, 4) as i8),
                         register(bits(src as i32, 16, 4) as i8),
                         ImmOrReg::imm(val))
        },
        
        0b111010000111_0000_0000000000000000...0b111010000111_1111_1111111111111111 |
        0b111010001111_0000_0000000000000000...0b111010001111_1111_1111111111111111 |
        0b111010010101_0000_0000000000000000...0b111010010101_1111_1111111111111111 |
        0b111010011101_0000_0000000000000000...0b111010011101_1111_1111111111111111 |
        0b111010010111_0000_0000000000000000...0b111010010111_1111_1111111111111111 |
        0b111010011111_0000_0000000000000000...0b111010011111_1111_1111111111111111 => {
            let mode = match (((src >> 23) & 1) != 0, ((src >> 21) & 1) != 0) { // PW
                (true, false) => StoreDoubleMode::Offset,
                (false, true) => StoreDoubleMode::PostIndex,
                (true, true)  => StoreDoubleMode::PreIndex,
                _ => return context.unpredictable(),
            };
            
            let neg = ((src >> 24) & 1) != 0;
            let val = bits(src as i32, 0, 8);
            let val = if neg { -val } else { val };

            context.ldrd(INST_NORMAL, mode,
                         register(bits(src as i32, 12, 4) as i8),
                         register(bits(src as i32, 8, 4) as i8),
                         register(bits(src as i32, 16, 4) as i8),
                         ImmOrReg::imm(val))
        },
            
        0b111010001100_0000_0000000000000000...0b111010001100_1111_1111111111111111 =>
            match bits(src as i32, 4, 4) {
                0b0100 => context.strex(INST_BYTE,
                                        register(bits(src as i32, 0, 4) as i8),
                                        register(bits(src as i32, 12, 4) as i8),
                                        ImmOrReg::register(bits(src as i32, 16, 4) as i8),
                                        ImmOrReg::imm(0)),
                
                0b0101 => context.strex(INST_HALF,
                                        register(bits(src as i32, 0, 4) as i8),
                                        register(bits(src as i32, 12, 4) as i8),
                                        ImmOrReg::register(bits(src as i32, 16, 4) as i8),
                                        ImmOrReg::imm(0)),

                0b0111 => context.strexd(INST_NORMAL,
                                         register(bits(src as i32, 0, 4) as i8),
                                         register(bits(src as i32, 12, 4) as i8),
                                         register(bits(src as i32, 8, 4) as i8),
                                         register(bits(src as i32, 16, 4) as i8)),

                0b1000 => context.str(INST_BYTE | INST_ACQUIRE,
                                      register(bits(src as i32, 12, 4) as i8),
                                      ImmOrReg::register(bits(src as i32, 16, 4) as i8),
                                      ImmOrReg::imm(0)),
                
                0b1001 => context.str(INST_HALF | INST_ACQUIRE,
                                      register(bits(src as i32, 12, 4) as i8),
                                      ImmOrReg::register(bits(src as i32, 16, 4) as i8),
                                      ImmOrReg::imm(0)),
                
                0b1010 => context.str(INST_ACQUIRE,
                                      register(bits(src as i32, 12, 4) as i8),
                                      ImmOrReg::register(bits(src as i32, 16, 4) as i8),
                                      ImmOrReg::imm(0)),

                0b1100 => context.strex(INST_BYTE | INST_ACQUIRE,
                                        register(bits(src as i32, 0, 4) as i8),
                                        register(bits(src as i32, 12, 4) as i8),
                                        ImmOrReg::register(bits(src as i32, 16, 4) as i8),
                                        ImmOrReg::imm(0)),
                
                0b1101 => context.strex(INST_HALF | INST_ACQUIRE,
                                        register(bits(src as i32, 0, 4) as i8),
                                        register(bits(src as i32, 12, 4) as i8),
                                        ImmOrReg::register(bits(src as i32, 16, 4) as i8),
                                        ImmOrReg::imm(0)),
                
                0b1110 => context.strex(INST_ACQUIRE,
                                        register(bits(src as i32, 0, 4) as i8),
                                        register(bits(src as i32, 12, 4) as i8),
                                        ImmOrReg::register(bits(src as i32, 16, 4) as i8),
                                        ImmOrReg::imm(0)),

                0b1111 => context.strexd(INST_ACQUIRE,
                                         register(bits(src as i32, 0, 4) as i8),
                                         register(bits(src as i32, 12, 4) as i8),
                                         register(bits(src as i32, 8, 4) as i8),
                                         register(bits(src as i32, 16, 4) as i8)),

                _ => panic!("thumb store release parse fail"),
            },
        
        0b111010001101_0000_0000000000000000...0b111010001101_1111_1111111111111111 => 
            match bits(src as i32, 4, 4) {
                0b0000 => context.tb(INST_BYTE,
                                     register(bits(src as i32, 16, 4) as i8),
                                     register(bits(src as i32, 0, 4) as i8)),
                
                0b0001 => context.tb(INST_HALF,
                                     register(bits(src as i32, 16, 4) as i8),
                                     register(bits(src as i32, 0, 4) as i8)),

                0b0100 => context.strex(INST_BYTE,
                                        register(bits(src as i32, 0, 4) as i8),
                                        register(bits(src as i32, 12, 4) as i8),
                                        ImmOrReg::register(bits(src as i32, 16, 4) as i8),
                                        ImmOrReg::imm(0)),
                
                0b0101 => context.strex(INST_HALF,
                                        register(bits(src as i32, 0, 4) as i8),
                                        register(bits(src as i32, 12, 4) as i8),
                                        ImmOrReg::register(bits(src as i32, 16, 4) as i8),
                                        ImmOrReg::imm(0)),

                0b0111 => context.strexd(INST_NORMAL,
                                         register(bits(src as i32, 0, 4) as i8),
                                         register(bits(src as i32, 12, 4) as i8),
                                         register(bits(src as i32, 8, 4) as i8),
                                         register(bits(src as i32, 16, 4) as i8)),

                0b1000 => context.ldr(INST_BYTE | INST_ACQUIRE,
                                      register(bits(src as i32, 12, 4) as i8),
                                      ImmOrReg::register(bits(src as i32, 16, 4) as i8),
                                      ImmOrReg::imm(0)),
                
                0b1001 => context.ldr(INST_HALF | INST_ACQUIRE,
                                      register(bits(src as i32, 12, 4) as i8),
                                      ImmOrReg::register(bits(src as i32, 16, 4) as i8),
                                      ImmOrReg::imm(0)),
                
                0b1010 => context.ldr(INST_ACQUIRE,
                                      register(bits(src as i32, 12, 4) as i8),
                                      ImmOrReg::register(bits(src as i32, 16, 4) as i8),
                                      ImmOrReg::imm(0)),

                0b1100 => context.ldrex(INST_BYTE | INST_ACQUIRE,
                                        register(bits(src as i32, 12, 4) as i8),
                                        ImmOrReg::register(bits(src as i32, 16, 4) as i8),
                                        ImmOrReg::imm(0)),
                
                0b1101 => context.ldrex(INST_HALF | INST_ACQUIRE,
                                        register(bits(src as i32, 12, 4) as i8),
                                        ImmOrReg::register(bits(src as i32, 16, 4) as i8),
                                        ImmOrReg::imm(0)),
                
                0b1110 => context.ldrex(INST_ACQUIRE,
                                        register(bits(src as i32, 12, 4) as i8),
                                        ImmOrReg::register(bits(src as i32, 16, 4) as i8),
                                        ImmOrReg::imm(0)),

                0b1111 => context.ldrexd(INST_ACQUIRE,
                                         register(bits(src as i32, 12, 4) as i8),
                                         register(bits(src as i32, 8, 4) as i8),
                                         register(bits(src as i32, 16, 4) as i8)),

                _ => panic!("thumb load acquire parse fail"),
            },
            
        _ => context.undefined(),
    }
}

