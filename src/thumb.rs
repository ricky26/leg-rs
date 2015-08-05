// Parser for the THUMB-2 instruction set

use std::fmt;

use super::*;
use super::{register, condition, extend_signed};
use super::disasm::Disassembler;

#[inline]
/// Extract bits from a source integer.
fn bits<T>(src: T, start: T, count: T) -> T
    where T: Int
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
                        Shifted(decode_imm_shift(bits(src as i32, 11, 2), bits(src as i32, 6, 5)),
                                ImmOrReg::register(((src >> 3) & 7) as i8))),

        0b0001100_000000000...0b0001100_111111111 =>
            context.add(INST_SET_FLAGS,
                        register((src & 7) as i8),
                        ImmOrReg::register(((src >> 3) & 7) as i8),
                        Shifted(Shift::none(),
                                ImmOrReg::imm(((src >> 6) & 7) as i32))),

        0b0001101_000000000...0b0001101_111111111 =>
            context.sub(INST_SET_FLAGS,
                        register((src & 7) as i8),
                        ImmOrReg::register(((src >> 3) & 7) as i8),
                        Shifted(Shift::none(),
                                ImmOrReg::register(((src >> 6) & 7) as i8))),
        
        0b0001110_000000000...0b0001110_111111111 =>
            context.add(INST_SET_FLAGS,
                        register((src & 7) as i8),
                        ImmOrReg::register(((src >> 3) & 7) as i8),
                        Shifted(Shift::none(),
                                ImmOrReg::imm(((src >> 6) & 7) as i32))),
            
        0b0001111_000000000...0b0001111_111111111 =>
            context.sub(INST_SET_FLAGS,
                        register((src & 7) as i8),
                        ImmOrReg::register(((src >> 3) & 7) as i8),
                        Shifted(Shift::none(),
                                ImmOrReg::imm(((src >> 6) & 7) as i32))),
        
        0b00100_00000000000...0b00100_11111111111 =>
            context.mov(INST_SET_FLAGS,
                        register(((src >> 8) & 7) as i8),
                        Shifted(Shift::none(),
                                ImmOrReg::imm((src & 0xff) as i32))),
        
        0b00101_00000000000...0b00101_11111111111 =>
            context.cmp(INST_NORMAL,
                        register(((src >> 8) & 7) as i8),
                        Shifted(Shift::none(),
                                ImmOrReg::imm((src & 0xff) as i32))),
        
        0b00110_00000000000...0b00110_11111111111 =>
            context.add(INST_SET_FLAGS,
                        register(((src >> 8) & 7) as i8),
                        ImmOrReg::register(((src >> 8) & 7) as i8),
                        Shifted(Shift::none(),
                                ImmOrReg::imm((src & 0xff) as i32))),
        
        0b00111_00000000000...0b00111_11111111111 =>
            context.sub(INST_SET_FLAGS,
                        register(((src >> 8) & 7) as i8),
                        ImmOrReg::register(((src >> 8) & 7) as i8),
                        Shifted(Shift::none(),
                                ImmOrReg::imm((src & 0xff) as i32))),

        //
        // F3.2.2 Data-Processing
        //
        
        0b0100000000_000000...0b0100000000_111111 =>
            context.and(INST_SET_FLAGS,
                        register((src & 7) as i8),
                        ImmOrReg::register((src & 7) as i8),
                        Shifted(Shift::none(),
                                ImmOrReg::register(((src >> 3) & 7) as i8))),
        
        0b0100000001_000000...0b0100000001_111111 =>
            context.eor(INST_SET_FLAGS,
                        register((src & 7) as i8),
                        ImmOrReg::register((src & 7) as i8),
                        Shifted(Shift::none(),
                                ImmOrReg::register(((src >> 3) & 7) as i8))),

        0b010000001_0000000...0b010000001_1111111 |
        0b0100000100_000000...0b0100000100_111111 |
        0b0100000111_000000...0b0100000111_111111 =>
            context.mov(INST_SET_FLAGS,
                        register((src & 7) as i8),
                        Shifted(decode_reg_shift(bits(src as i32, 6, 4), register(bits(src as i32, 3, 3) as i8)),
                                ImmOrReg::register((src & 7) as i8))),

        0b0100000101_000000...0b0100000101_111111 =>
            context.adc(INST_SET_FLAGS,
                        register((src & 7) as i8),
                        ImmOrReg::register((src & 7) as i8),
                        Shifted(Shift::none(),
                                ImmOrReg::register(((src >> 3) & 7) as i8))),
        
        0b0100000110_000000...0b0100000110_111111 =>
            context.sbc(INST_SET_FLAGS,
                        register((src & 7) as i8),
                        ImmOrReg::register((src & 7) as i8),
                        Shifted(Shift::none(),
                                ImmOrReg::register(((src >> 3) & 7) as i8))),
        
        0b0100001000_000000...0b0100001000_111111 =>
            context.tst(INST_NORMAL,
                        register((src & 7) as i8),
                        Shifted(Shift::none(),
                                ImmOrReg::register(((src >> 3) & 7) as i8))),
        
        0b0100001001_000000...0b0100001001_111111 =>
            context.rsb(INST_SET_FLAGS,
                        register((src & 7) as i8),
                        ImmOrReg::register(((src >> 3) & 7) as i8),
                        Shifted(Shift::none(),
                                ImmOrReg::imm(0))),
        
        0b0100001010_000000...0b0100001010_111111 =>
            context.cmp(INST_NORMAL,
                        register((src & 7) as i8),
                        Shifted(Shift::none(),
                                ImmOrReg::register(((src >> 3) & 7) as i8))),
        
        0b0100001011_000000...0b0100001011_111111 =>
            context.cmn(INST_NORMAL,
                        register((src & 7) as i8),
                        Shifted(Shift::none(),
                                ImmOrReg::register(((src >> 3) & 7) as i8))),
        
        0b0100001100_000000...0b0100001100_111111 =>
            context.orr(INST_SET_FLAGS,
                        register((src & 7) as i8),
                        ImmOrReg::register((src & 7) as i8),
                        Shifted(Shift::none(),
                                ImmOrReg::register(((src >> 3) & 7) as i8))),
        
        0b0100001101_000000...0b0100001101_111111 =>
            context.mul(INST_SET_FLAGS,
                        register((src & 7) as i8),
                        ImmOrReg::register((src & 7) as i8),
                        ImmOrReg::register(((src >> 3) & 7) as i8)),
        
        0b0100001110_000000...0b0100001110_111111 =>
            context.bic(INST_SET_FLAGS,
                        register((src & 7) as i8),
                        ImmOrReg::register((src & 7) as i8),
                        Shifted(Shift::none(),
                                ImmOrReg::register(((src >> 3) & 7) as i8))),
        
        0b0100001111_000000...0b0100001111_111111 =>
            context.mvn(INST_SET_FLAGS,
                        register((src & 7) as i8),
                        Shifted(Shift::none(),
                                ImmOrReg::register(((src >> 3) & 7) as i8))),

        //
        // F3.2.3 - Special data instruction and branch and exchange
        //

        0b01000100_00000000...0b01000100_11111111 => {
            let rdn = register(((src & 7) | ((src >> 4) & 0x80)) as i8);
            context.add(INST_SET_FLAGS,
                        rdn,
                        ImmOrReg::Reg(rdn),
                        Shifted(Shift::none(),
                                ImmOrReg::register(((src >> 3) & 0xf) as i8)))
        },

        0b01000101_00000000...0b01000101_11111111 =>
            context.cmp(INST_NORMAL,
                        register(((src & 7) | ((src >> 4) & 0x80)) as i8),
                        Shifted(Shift::none(),
                                ImmOrReg::register(((src >> 3) & 0xf) as i8))),

        0b01000110_00000000...0b01000110_11111111 =>
            context.mov(INST_NORMAL,
                        register(((src & 7) | ((src >> 4) & 0x80)) as i8),
                        Shifted(Shift::none(),
                                ImmOrReg::register(((src >> 3) & 0xf) as i8))),

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
            context.add(INST_NORMAL,
                        register(((src >> 8) & 0x7) as i8),
                        ImmOrReg::Reg(Register::PC),
                        Shifted(Shift::none(),
                                ImmOrReg::imm((src & 0xff) as i32))),
        
        // ADD (SP+imm)
        0b10101_00000000000...0b10101_11111111111 =>
            context.add(INST_NORMAL,
                        register(((src >> 8) & 7) as i8),
                        ImmOrReg::Reg(Register::SP),
                        Shifted(Shift::none(),
                                ImmOrReg::imm((src & 0xff) as i32))),

        //
        // F3.2.5 - Miscellaneous 16-bit instructions
        //

        0b101100000_0000000...0b101100000_1111111 =>
            context.add(INST_NORMAL,
                        Register::SP,
                        ImmOrReg::Reg(Register::SP),
                        Shifted(Shift::none(),
                                ImmOrReg::imm((src & 0x7f) as i32))),
        
        0b101100001_0000000...0b101100001_1111111 =>
            context.sub(INST_NORMAL,
                        Register::SP,
                        ImmOrReg::Reg(Register::SP),
                        Shifted(Shift::none(),
                                ImmOrReg::imm((src & 0x7f) as i32))),
        
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

        0b11011110_00000000...0b11011110_11111111 => context.undefined("UDF"),
        0b11011111_00000000...0b11011111_11111111 => context.svc((src & 0xff) as i8),

        0b1101_000000000000...0b1101_111111111111  =>
            context.b(INST_NORMAL,
                      condition(((src >> 8) & 0xf) as i8),
                      ImmOrReg::imm(((src & 0xff) << 1) as i32)),
            
        0b11100_00000000000...0b11100_11111111111 =>
            context.b(INST_NORMAL,
                      Condition::AL,
                      ImmOrReg::imm((((src & 0x3ff) << 2) as i32) >> 1)),
        
        _ => context.undefined("16-bit thumb"),
    }
}

fn parse_data_processing<T: ExecutionContext>(context: &mut T, src: u32, imm: Shifted) -> Result<()> {
    let s32 = src as i32;
    
    let s = ((src >> 20) & 1) != 0;
    let rd = bits(s32, 8, 4) as i8;
    let rn = bits(s32, 16, 0) as i8;
    let op = bits(s32, 21, 4);
    
    let flags = if s { INST_SET_FLAGS } else { INST_NORMAL };

    match op {
        0b0000 => if rd != 0b1111 {
            context.and(flags, register(rd), ImmOrReg::register(rn), imm)
        } else {
            context.tst(flags, register(rn), imm)
        },

        0b0001 => context.bic(flags, register(rd), ImmOrReg::register(rn), imm),

        0b0010 => if rn != 0b1111 {
            context.orr(flags, register(rd), ImmOrReg::register(rn), imm)
        } else {
            context.mov(flags, register(rd), imm)
        },

        0b0011 => if rn != 0b1111 {
            context.orn(flags, register(rd), ImmOrReg::register(rn), imm)
        } else {
            context.mvn(flags, register(rd), imm)
        },

        0b0100 => if rd != 0b1111 {
            context.eor(flags, register(rd), ImmOrReg::register(rn), imm)
        } else {
            context.teq(flags, register(rn), imm)
        },

        0b1000 => if rd != 0b1111 {
            context.add(flags, register(rd), ImmOrReg::register(rn), imm)
        } else {
            context.cmn(flags, register(rn), imm)
        },

        0b1010 => context.adc(flags, register(rd), ImmOrReg::register(rn), imm),
        0b1011 => context.sbc(flags, register(rd), ImmOrReg::register(rn), imm),

        0b1101 => if rd != 0b1111 {
            context.sub(flags, register(rd), ImmOrReg::register(rn), imm)
        } else {
            context.cmp(flags, register(rn), imm)
        },
        
        0b1110 => context.rsb(flags, register(rd), ImmOrReg::register(rn), imm),

        _ => context.undefined("thumb data-processing operation"),
    }
}

/// Execute a THUMB-32 instruction as an integer.
pub fn execute_32<T: ExecutionContext>(src: u32, context: &mut T) -> Result<()> {
    let s32 = src as i32;
    
    match src {
        0...0b11100_11111111111_1111111111111111 => panic!("invalid 32-bit thumb instruction"),
        
        0b1110100010_000000_0000000000000000...0b1110100010_111111_1111111111111111 |
        0b1110100100_000000_0000000000000000...0b1110100100_111111_1111111111111111 => {
            let load = ((src >> 20) & 1) != 0;
            let reg = register(bits(s32, 16, 4) as i8);
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
            let reg = register(bits(s32, 16, 4) as i8);
            
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
                context.srs(flags, reg, bits(s32, 0, 5) as i8)
            }
        },

        // STREX
        0b111010000100_0000_0000000000000000...0b111010000100_1111_1111111111111111 =>
            context.strex(INST_NORMAL,
                          register(bits(s32, 8, 4) as i8),
                          register(bits(s32, 12, 4) as i8),
                          ImmOrReg::register(bits(s32, 16, 4) as i8),
                          ImmOrReg::imm(bits(s32, 0, 8))),
        // LDREX
        0b111010000101_0000_0000000000000000...0b111010000101_1111_1111111111111111 =>
            context.ldrex(INST_NORMAL,
                          register(bits(s32, 12, 4) as i8),
                          ImmOrReg::register(bits(s32, 16, 4) as i8),
                          ImmOrReg::imm(bits(s32, 0, 8))),

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
            let val = bits(s32, 0, 8);
            let val = if neg { -val } else { val };

            context.strd(INST_NORMAL, mode,
                         register(bits(s32, 12, 4) as i8),
                         register(bits(s32, 8, 4) as i8),
                         register(bits(s32, 16, 4) as i8),
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
            let val = bits(s32, 0, 8);
            let val = if neg { -val } else { val };

            context.ldrd(INST_NORMAL, mode,
                         register(bits(s32, 12, 4) as i8),
                         register(bits(s32, 8, 4) as i8),
                         register(bits(s32, 16, 4) as i8),
                         ImmOrReg::imm(val))
        },
            
        0b111010001100_0000_0000000000000000...0b111010001100_1111_1111111111111111 =>
            match bits(s32, 4, 4) {
                0b0100 => context.strex(INST_BYTE,
                                        register(bits(s32, 0, 4) as i8),
                                        register(bits(s32, 12, 4) as i8),
                                        ImmOrReg::register(bits(s32, 16, 4) as i8),
                                        ImmOrReg::imm(0)),
                
                0b0101 => context.strex(INST_HALF,
                                        register(bits(s32, 0, 4) as i8),
                                        register(bits(s32, 12, 4) as i8),
                                        ImmOrReg::register(bits(s32, 16, 4) as i8),
                                        ImmOrReg::imm(0)),

                0b0111 => context.strexd(INST_NORMAL,
                                         register(bits(s32, 0, 4) as i8),
                                         register(bits(s32, 12, 4) as i8),
                                         register(bits(s32, 8, 4) as i8),
                                         register(bits(s32, 16, 4) as i8)),

                0b1000 => context.str(INST_BYTE | INST_ACQUIRE,
                                      register(bits(s32, 12, 4) as i8),
                                      ImmOrReg::register(bits(s32, 16, 4) as i8),
                                      ImmOrReg::imm(0)),
                
                0b1001 => context.str(INST_HALF | INST_ACQUIRE,
                                      register(bits(s32, 12, 4) as i8),
                                      ImmOrReg::register(bits(s32, 16, 4) as i8),
                                      ImmOrReg::imm(0)),
                
                0b1010 => context.str(INST_ACQUIRE,
                                      register(bits(s32, 12, 4) as i8),
                                      ImmOrReg::register(bits(s32, 16, 4) as i8),
                                      ImmOrReg::imm(0)),

                0b1100 => context.strex(INST_BYTE | INST_ACQUIRE,
                                        register(bits(s32, 0, 4) as i8),
                                        register(bits(s32, 12, 4) as i8),
                                        ImmOrReg::register(bits(s32, 16, 4) as i8),
                                        ImmOrReg::imm(0)),
                
                0b1101 => context.strex(INST_HALF | INST_ACQUIRE,
                                        register(bits(s32, 0, 4) as i8),
                                        register(bits(s32, 12, 4) as i8),
                                        ImmOrReg::register(bits(s32, 16, 4) as i8),
                                        ImmOrReg::imm(0)),
                
                0b1110 => context.strex(INST_ACQUIRE,
                                        register(bits(s32, 0, 4) as i8),
                                        register(bits(s32, 12, 4) as i8),
                                        ImmOrReg::register(bits(s32, 16, 4) as i8),
                                        ImmOrReg::imm(0)),

                0b1111 => context.strexd(INST_ACQUIRE,
                                         register(bits(s32, 0, 4) as i8),
                                         register(bits(s32, 12, 4) as i8),
                                         register(bits(s32, 8, 4) as i8),
                                         register(bits(s32, 16, 4) as i8)),

                _ => panic!("thumb store release parse fail"),
            },
        
        0b111010001101_0000_0000000000000000...0b111010001101_1111_1111111111111111 => 
            match bits(s32, 4, 4) {
                0b0000 => context.tb(INST_BYTE,
                                     register(bits(s32, 16, 4) as i8),
                                     register(bits(s32, 0, 4) as i8)),
                
                0b0001 => context.tb(INST_HALF,
                                     register(bits(s32, 16, 4) as i8),
                                     register(bits(s32, 0, 4) as i8)),

                0b0100 => context.strex(INST_BYTE,
                                        register(bits(s32, 0, 4) as i8),
                                        register(bits(s32, 12, 4) as i8),
                                        ImmOrReg::register(bits(s32, 16, 4) as i8),
                                        ImmOrReg::imm(0)),
                
                0b0101 => context.strex(INST_HALF,
                                        register(bits(s32, 0, 4) as i8),
                                        register(bits(s32, 12, 4) as i8),
                                        ImmOrReg::register(bits(s32, 16, 4) as i8),
                                        ImmOrReg::imm(0)),

                0b0111 => context.strexd(INST_NORMAL,
                                         register(bits(s32, 0, 4) as i8),
                                         register(bits(s32, 12, 4) as i8),
                                         register(bits(s32, 8, 4) as i8),
                                         register(bits(s32, 16, 4) as i8)),

                0b1000 => context.ldr(INST_BYTE | INST_ACQUIRE,
                                      register(bits(s32, 12, 4) as i8),
                                      ImmOrReg::register(bits(s32, 16, 4) as i8),
                                      ImmOrReg::imm(0)),
                
                0b1001 => context.ldr(INST_HALF | INST_ACQUIRE,
                                      register(bits(s32, 12, 4) as i8),
                                      ImmOrReg::register(bits(s32, 16, 4) as i8),
                                      ImmOrReg::imm(0)),
                
                0b1010 => context.ldr(INST_ACQUIRE,
                                      register(bits(s32, 12, 4) as i8),
                                      ImmOrReg::register(bits(s32, 16, 4) as i8),
                                      ImmOrReg::imm(0)),

                0b1100 => context.ldrex(INST_BYTE | INST_ACQUIRE,
                                        register(bits(s32, 12, 4) as i8),
                                        ImmOrReg::register(bits(s32, 16, 4) as i8),
                                        ImmOrReg::imm(0)),
                
                0b1101 => context.ldrex(INST_HALF | INST_ACQUIRE,
                                        register(bits(s32, 12, 4) as i8),
                                        ImmOrReg::register(bits(s32, 16, 4) as i8),
                                        ImmOrReg::imm(0)),
                
                0b1110 => context.ldrex(INST_ACQUIRE,
                                        register(bits(s32, 12, 4) as i8),
                                        ImmOrReg::register(bits(s32, 16, 4) as i8),
                                        ImmOrReg::imm(0)),

                0b1111 => context.ldrexd(INST_ACQUIRE,
                                         register(bits(s32, 12, 4) as i8),
                                         register(bits(s32, 8, 4) as i8),
                                         register(bits(s32, 16, 4) as i8)),

                _ => panic!("thumb load acquire parse fail"),
            },

        //
        // F3.3.11 Data-processing (Shifted register)
        //
        
        0b11101010110_00000_0000000000000000...0b11101010110_11111_1111111111111111 => {
            let imm = (bits(s32, 16, 4) << 4) | bits(s32, 0, 4);
            let rd = bits(s32, 8, 4);
            let rn = bits(s32, 16, 4);

            let tbform = ((src >> 5) & 1) != 0;
            let flags = if tbform { INST_TBFORM } else { INST_NORMAL };

            let shift = Shift(if tbform { ShiftType::ASR } else { ShiftType::LSL }, ImmOrReg::imm(imm));

            context.pkh(flags,
                        register(rd as i8),
                        register(rn as i8),
                        Shifted(shift, ImmOrReg::register(bits(s32, 0, 4) as i8)))
        },
        
        0b1110101_000000000_0000000000000000...0b1110101_111111111_1111111111111111 => {
            let imm = (bits(s32, 16, 4) << 4) | bits(s32, 0, 4);
            let shift_type = bits(s32, 4, 2);

            parse_data_processing(context, src, 
                                  Shifted(decode_imm_shift(shift_type, imm),
                                          ImmOrReg::register(bits(s32, 8, 4) as i8)))
        },

        //
        // F3.3.15 - Coprocessor, Advanced SIMD and FP
        //
        
        0b111011_0000000000_0000000000000000...0b111011_1111111111_1111111111111111 |
        0b111111_0000000000_0000000000000000...0b111111_1111111111_1111111111111111 => {
            let coproc = bits(s32, 8, 4);

            if (coproc & 0b1110) != 0b1010 {
                // coproc
                
                let alt = ((src >> 28) & 1) != 0;
                let flags = if alt { INST_ALT } else { INST_NORMAL };
                let coproc = coproc as i8;
                
                match bits(s32, 20, 6) {
                    0b000100...0b000101 => {
                        let crm = bits(s32, 0, 4) as i8;
                        let opcode = bits(s32, 4, 4) as i8;
                        let rt = register(bits(s32, 12, 4) as i8);
                        let rt2 = register(bits(s32, 16, 4) as i8);
                        
                        let l = ((src >> 20) & 1) != 0;
                        
                        if !l {
                            context.mcrr(flags, coproc, opcode, crm, rt, rt2)
                        } else {
                            context.mcrr(flags, coproc, opcode, crm, rt, rt2)
                        }
                    },
                    
                    0b0_00000...0b0_11111 => {
                        let p = ((src >> 24) & 1) != 0;
                        let u = ((src >> 23) & 1) != 0;
                        let d = ((src >> 22) & 1) != 0;
                        let w = ((src >> 21) & 1) != 0;
                        let l = ((src >> 20) & 1) != 0;

                        let imm = bits(s32, 0, 8) << 2;

                        let flags = flags | if d { INST_LONG } else { INST_NORMAL };
                        let flags = flags | if p && w { INST_WRITEBACK } else { INST_NORMAL };
                        let flags = flags | if !p { INST_PREINC } else { INST_NORMAL };

                        let crd = bits(s32, 12, 4) as i8;

                        let (imm, option) = if p || !u || w {
                            (imm, 0u8)
                        } else {
                            (0, imm as u8)
                        };

                        if !l {
                            context.stc(flags,
                                        coproc,
                                        crd,
                                        register(bits(s32, 16, 4) as i8),
                                        ImmOrReg::imm(imm),
                                        option)
                        } else {
                            context.ldc(flags,
                                        coproc,
                                        crd,
                                        register(bits(s32, 16, 4) as i8),
                                        ImmOrReg::imm(imm),
                                        option)
                        }
                    },

                    0b10_0000...0b10_1111 => {
                        if ((s32 >> 4) & 1) != 0 {
                            let l = ((src >> 20) & 1) != 0;
                            let crm = bits(s32, 0, 4) as i8;
                            let crn = bits(s32, 16, 4) as i8;
                            let opc1 = bits(s32, 5, 3) as i8;
                            let opc2 = bits(s32, 21, 3) as i8;
                            let rc = register(bits(s32, 12, 4) as i8);

                            if l {
                                context.mrc(flags, coproc, rc, opc1, crn, opc2, crm)
                            } else {
                                context.mcr(flags, coproc, rc, opc1, crn, opc2, crm)
                            }
                        } else {
                            let crm = bits(s32, 0, 4) as i8;
                            let crn = bits(s32, 16, 4) as i8;
                            let crd = bits(s32, 12, 4) as i8;
                            
                            let opc1 = bits(s32, 5, 3) as i8;
                            let opc2 = bits(s32, 20, 4) as i8;

                            context.cdp(flags, coproc, crd, opc2, crm, opc1, crn)
                        }
                    },

                    _ => context.undefined("coproc"),
                }
            } else {
                // TODO: FP
                context.unimplemented("FP 1")
            }
        },

        //
        // F3.3.1 Data-processing (modified immediate)
        //

        0b11110_00000000000_0000000000000000...0b11110_11111111111_1111111111111111 if ((src >> 15) & 1) == 0 => {
            if bits(s32, 25, 1) == 0 {
                // Data-processing (modified immediate)
                
                let base_imm = bits(s32, 0, 8);
                let mod_type = (bits(s32, 26, 1) << 4) | (bits(s32, 12, 3) << 1) | (s32 & 1);
                let imm;

                match mod_type {
                    0 | 1 => imm = base_imm,
                    2 | 3 => imm = base_imm | (base_imm << 16),
                    4 | 5 => imm = (base_imm << 8) | (base_imm << 24),
                    6 | 7 => imm = base_imm | (base_imm << 8) | (base_imm << 16) | (base_imm << 24),
                    x => {
                        let base_imm = base_imm | 0x80;
                        imm = base_imm << (24 - x)
                    },
                }

                parse_data_processing(context, src, Shifted(Shift::none(), ImmOrReg::imm(imm)))
            } else {
                // Data-processing (plain binary immediate)

                let s = bits(s32, 20, 1) != 0;
                let rd = bits(s32, 8, 4) as i8;
                let rn = bits(s32, 16, 4) as i8;
                let imm_a = extend_signed((bits(s32, 26, 1) << 11) | (bits(s32, 12, 3) << 8) | bits(s32, 0, 8), 12);
                let imm_b = extend_signed((bits(s32, 26, 1) << 15)
                                          | (bits(s32, 16, 4) << 11)
                                          | (bits(s32, 12, 3) << 8)
                                          | bits(s32, 0, 8), 16);

                let flags = if s { INST_SET_FLAGS } else { INST_NORMAL };

                match bits(s32, 20, 5) {
                    0b00000 => context.add(flags,
                                           register(rd),
                                           ImmOrReg::register(rn),
                                           Shifted(Shift::none(),
                                                   ImmOrReg::imm(imm_a))),

                    0b00100 => context.mov(flags,
                                           register(rd),
                                           Shifted(Shift::none(), ImmOrReg::imm(imm_b))),

                    0b01010 => context.sub(flags,
                                           register(rd),
                                           ImmOrReg::register(rn),
                                           Shifted(Shift::none(),
                                                   ImmOrReg::imm(imm_a))),

                    0b01100 => context.mov(flags | INST_TOP,
                                           register(rd),
                                           Shifted(Shift::none(), ImmOrReg::imm(imm_b << 16))),

                    0b10000 | 0b10010 => context.unimplemented("SSAT thumb-32"),

                    0b10100 => context.unimplemented("SBFX"),
                    0b10110 => context.unimplemented("BFI/C"),

                    0b11000 | 0b11010 => context.unimplemented("SAT"),
                    
                    0b11100 => context.unimplemented("UBFX"),
                    
                    _ => context.undefined("thumb data-processing (plain binary)"),
                }
            }
        },
        
        0b11110_00000000000_0000000000000000...0b11110_11111111111_1111111111111111 => {
            context.unimplemented("branches")
        },
        
        _ => context.undefined(""),
    }
}

