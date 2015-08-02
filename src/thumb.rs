// Parser for the THUMB-2 instruction set

use std::fmt;

use super::{
    Error, Result, ExecutionContext, Register, ImmOrReg, Condition,
    INST_NORMAL, INST_SET_FLAGS, INST_SIGNED, INST_WORD, INST_BYTE,
    register, condition,
};
use super::disasm::Disassembler;

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

pub fn execute_16<T: ExecutionContext>(src: u16, context: &mut T) -> Result<()> {
    match (src >> 9) & 0x7f {
        0b0000000 | 0b0000001 | 0b0000010 | 0b0000011 |
        0b0000100 | 0b0000101 | 0b0000110 | 0b0000111 |
        0b0001000 | 0b0001001 | 0b0001010 | 0b0001011 |
        0b0001100 | 0b0001101 | 0b0001110 | 0b0001111 |
        0b0010000 | 0b0010001 | 0b0010010 | 0b0010011 |
        0b0010100 | 0b0010101 | 0b0010110 | 0b0010111 |
        0b0011000 | 0b0011001 | 0b0011010 | 0b0011011 |
        0b0011100 | 0b0011101 | 0b0011110 | 0b0011111 => {
            match (src >> 9) & 0x1f {
                0b00000 | 0b00001 | 0b00010 | 0b00011 =>
                    context.lsl(INST_SET_FLAGS,
                                register((src & 7) as i8),
                                ImmOrReg::register(((src >> 3) & 7) as i8),
                                ImmOrReg::imm(((src >> 6) & 0x1f) as i8)),
                0b00100 | 0b00101 | 0b00110 | 0b00111 => 
                    context.lsr(INST_SET_FLAGS,
                                register((src & 7) as i8),
                                ImmOrReg::register(((src >> 3) & 7) as i8),
                                ImmOrReg::imm(((src >> 6) & 0x1f) as i8)),
                0b01000 | 0b01001 | 0b01010 | 0b01011 => 
                    context.asr(INST_SET_FLAGS,
                                register((src & 7) as i8),
                                ImmOrReg::register(((src >> 3) & 7) as i8),
                                ImmOrReg::imm(((src >> 6) & 0x1f) as i8)),
                0b01100 =>
                    context.add(INST_SET_FLAGS,
                                register((src & 7) as i8),
                                ImmOrReg::register(((src >> 3) & 7) as i8),
                                ImmOrReg::register(((src >> 6) & 7) as i8)),
                0b01101 => 
                    context.sub(INST_SET_FLAGS,
                                register((src & 7) as i8),
                                ImmOrReg::register(((src >> 3) & 7) as i8),
                                ImmOrReg::register(((src >> 6) & 7) as i8)),
                0b01110 =>
                    context.add(INST_SET_FLAGS,
                                register((src & 7) as i8),
                                ImmOrReg::register(((src >> 3) & 7) as i8),
                                ImmOrReg::imm(((src >> 6) & 7) as i32)),
                0b01111 =>
                    context.sub(INST_SET_FLAGS,
                                register((src & 7) as i8),
                                ImmOrReg::register(((src >> 3) & 7) as i8),
                                ImmOrReg::imm(((src >> 6) & 7) as i32)),
                0b10000 | 0b10001 | 0b10010 | 0b10011 =>
                    context.mov(INST_SET_FLAGS,
                                register(((src >> 8) & 7) as i8),
                                ImmOrReg::imm((src & 0xff) as i32)),
                0b10100 | 0b10101 | 0b10110 | 0b10111 =>
                    context.cmp(INST_NORMAL,
                                register(((src >> 8) & 7) as i8),
                                ImmOrReg::imm((src & 0xff) as i32)),
                0b11000 | 0b11001 | 0b11010 | 0b11011 =>
                    context.add(INST_SET_FLAGS,
                                register(((src >> 8) & 7) as i8),
                                ImmOrReg::register(((src >> 8) & 7) as i8),
                                ImmOrReg::imm((src & 0xff) as i32)),
                0b11100 | 0b11101 | 0b11110 | 0b11111 =>
                    context.sub(INST_SET_FLAGS,
                                register(((src >> 8) & 7) as i8),
                                ImmOrReg::register(((src >> 8) & 7) as i8),
                                ImmOrReg::imm((src & 0xff) as i32)),
                
                _ => panic!("invalid bit pattern: thumb 16-bit basic alu"),
            }
        },

        0b0100000 | 0b0100001 => {
            match (src >> 6) & 0xf {
                0b0000 => context.and(INST_SET_FLAGS,
                                      register((src & 7) as i8),
                                      ImmOrReg::register((src & 7) as i8),
                                      ImmOrReg::register(((src >> 3) & 7) as i8)),
                0b0001 => context.eor(INST_SET_FLAGS,
                                      register((src & 7) as i8),
                                      ImmOrReg::register((src & 7) as i8),
                                      ImmOrReg::register(((src >> 3) & 7) as i8)),
                0b0010 => context.lsl(INST_SET_FLAGS,
                                      register((src & 7) as i8),
                                      ImmOrReg::register((src & 7) as i8),
                                      ImmOrReg::register(((src >> 3) & 7) as i8)),
                0b0011 => context.lsr(INST_SET_FLAGS,
                                      register((src & 7) as i8),
                                      ImmOrReg::register((src & 7) as i8),
                                      ImmOrReg::register(((src >> 3) & 7) as i8)),
                0b0100 => context.asr(INST_SET_FLAGS,
                                      register((src & 7) as i8),
                                      ImmOrReg::register((src & 7) as i8),
                                      ImmOrReg::register(((src >> 3) & 7) as i8)),
                0b0101 => context.adc(INST_SET_FLAGS,
                                      register((src & 7) as i8),
                                      ImmOrReg::register((src & 7) as i8),
                                      ImmOrReg::register(((src >> 3) & 7) as i8)),
                0b0110 => context.sbc(INST_SET_FLAGS,
                                      register((src & 7) as i8),
                                      ImmOrReg::register((src & 7) as i8),
                                      ImmOrReg::register(((src >> 3) & 7) as i8)),
                0b0111 => context.ror(INST_SET_FLAGS,
                                      register((src & 7) as i8),
                                      ImmOrReg::register((src & 7) as i8),
                                      ImmOrReg::register(((src >> 3) & 7) as i8)),
                0b1000 => context.test(INST_NORMAL,
                                       register((src & 7) as i8),
                                       ImmOrReg::register(((src >> 3) & 7) as i8)),
                0b1001 => context.rsb(INST_SET_FLAGS,
                                      register((src & 7) as i8),
                                      ImmOrReg::register(((src >> 3) & 7) as i8),
                                      ImmOrReg::imm(0)),
                0b1010 => context.cmp(INST_NORMAL,
                                      register((src & 7) as i8),
                                      ImmOrReg::register(((src >> 3) & 7) as i8)),
                0b1011 => context.cmn(INST_NORMAL,
                                      register((src & 7) as i8),
                                      ImmOrReg::register(((src >> 3) & 7) as i8)),
                0b1100 => context.orr(INST_SET_FLAGS,
                                      register((src & 7) as i8),
                                      ImmOrReg::register((src & 7) as i8),
                                      ImmOrReg::register(((src >> 3) & 7) as i8)),
                0b1101 => context.mul(INST_SET_FLAGS,
                                      register((src & 7) as i8),
                                      ImmOrReg::register((src & 7) as i8),
                                      ImmOrReg::register(((src >> 3) & 7) as i8)),
                0b1110 => context.bic(INST_SET_FLAGS,
                                      register((src & 7) as i8),
                                      ImmOrReg::register((src & 7) as i8),
                                      ImmOrReg::register(((src >> 3) & 7) as i8)),
                0b1111 => context.mvn(INST_SET_FLAGS,
                                      register((src & 7) as i8),
                                      ImmOrReg::register(((src >> 3) & 7) as i8)),

                _ => panic!("invalid bit pattern: thumb 16-bit data processing"),
            }
        },

        0b0100010 | 0b0100011 => {
            match (src >> 6) & 0x0f {
                0b0000 | 0b0001 | 0b0010 | 0b0011 => {
                    let rdn = register(((src & 7) | ((src >> 4) & 0x80)) as i8);
                    context.add(INST_SET_FLAGS,
                                rdn,
                                ImmOrReg::Reg(rdn),
                                ImmOrReg::register(((src >> 3) & 0xf) as i8))
                },
                
                0b0100 => context.unpredictable(),
                
                0b0101 | 0b0110 | 0b0111 =>
                    context.cmp(INST_NORMAL,
                                register(((src & 7) | ((src >> 4) & 0x80)) as i8),
                                ImmOrReg::register(((src >> 3) & 0xf) as i8)),

                0b1000 | 0b1001 | 0b1010 | 0b1011 =>
                    context.mov(INST_NORMAL,
                                register(((src & 7) | ((src >> 4) & 0x80)) as i8),
                                ImmOrReg::register(((src >> 3) & 0xf) as i8)),

                0b1100 | 0b1101 =>
                    context.b(Condition::AL,
                              ImmOrReg::register(((src >> 3) & 0xf) as i8),
                              false, true),
            
                0b1110 | 0b1111 =>
                    context.b(Condition::AL,
                              ImmOrReg::register(((src >> 3) & 0xf) as i8),
                              true, true),
                
                _ => panic!("invalid bit pattern: thumb 16-bit special data instructions"),                
            }
        },

        // Load literal

        0b0100100 | 0b0100101 | 0b0100110 | 0b0100111 =>
                context.ldr(INST_NORMAL,
                        register(((src >> 8) & 7) as i8),
                        ImmOrReg::Reg(Register::PC),
                        ImmOrReg::imm((src & 0xf) as i32)),

        // Load/Store single data item
        
        0b0101000 =>
            context.str(INST_NORMAL,
                        register((src & 7) as i8),
                        ImmOrReg::register(((src >> 3) & 7) as i8),
                        ImmOrReg::register(((src >> 6) & 7) as i8)),
        
        0b0101001 =>
            context.str(INST_WORD,
                        register((src & 7) as i8),
                        ImmOrReg::register(((src >> 3) & 7) as i8),
                        ImmOrReg::register(((src >> 6) & 7) as i8)),
        
        0b0101010 =>
            context.str(INST_WORD,
                        register((src & 7) as i8),
                        ImmOrReg::register(((src >> 3) & 7) as i8),
                        ImmOrReg::register(((src >> 6) & 7) as i8)),
        
        0b0101011 =>
            context.ldr(INST_BYTE | INST_SIGNED,
                        register((src & 7) as i8),
                        ImmOrReg::register(((src >> 3) & 7) as i8),
                        ImmOrReg::register(((src >> 6) & 7) as i8)),
        
        0b0101100 =>
            context.ldr(INST_NORMAL,
                        register((src & 7) as i8),
                        ImmOrReg::register(((src >> 3) & 7) as i8),
                        ImmOrReg::register(((src >> 6) & 7) as i8)),
        
        0b0101101 =>
            context.ldr(INST_WORD,
                        register((src & 7) as i8),
                        ImmOrReg::register(((src >> 3) & 7) as i8),
                        ImmOrReg::register(((src >> 6) & 7) as i8)),
        
        0b0101110 =>
            context.ldr(INST_BYTE,
                        register((src & 7) as i8),
                        ImmOrReg::register(((src >> 3) & 7) as i8),
                        ImmOrReg::register(((src >> 6) & 7) as i8)),
        
        0b0101111 =>
            context.ldr(INST_WORD | INST_SIGNED,
                        register((src & 7) as i8),
                        ImmOrReg::register(((src >> 3) & 7) as i8),
                        ImmOrReg::register(((src >> 6) & 7) as i8)),

        0b0110000 | 0b0110001 | 0b0110010 | 0b0110011 =>
            context.str(INST_NORMAL,
                        register((src & 7) as i8),
                        ImmOrReg::register(((src >> 3) & 7) as i8),
                        ImmOrReg::imm(((src >> 6) & 0x1f) as i32)),
        

        0b0110100 | 0b0110101 | 0b0110110 | 0b0110111 =>
            context.ldr(INST_NORMAL,
                        register((src & 7) as i8),
                        ImmOrReg::register(((src >> 3) & 7) as i8),
                        ImmOrReg::imm(((src >> 6) & 0x1f) as i32)),

        0b0111000 | 0b0111001 | 0b0111010 | 0b0111011 =>
            context.str(INST_BYTE,
                        register((src & 7) as i8),
                        ImmOrReg::register(((src >> 3) & 7) as i8),
                        ImmOrReg::imm(((src >> 6) & 0x1f) as i32)),
        

        0b0111100 | 0b0111101 | 0b0111110 | 0b0111111 =>
            context.ldr(INST_BYTE,
                        register((src & 7) as i8),
                        ImmOrReg::register(((src >> 3) & 7) as i8),
                        ImmOrReg::imm(((src >> 6) & 0x1f) as i32)),

        0b1000000 | 0b1000001 | 0b1000010 | 0b1000011 =>
            context.str(INST_WORD,
                        register((src & 7) as i8),
                        ImmOrReg::register(((src >> 3) & 7) as i8),
                        ImmOrReg::imm(((src >> 6) & 0x1f) as i32)),
        

        0b1000100 | 0b1000101 | 0b1000110 | 0b1000111 =>
            context.ldr(INST_WORD,
                        register((src & 7) as i8),
                        ImmOrReg::register(((src >> 3) & 7) as i8),
                        ImmOrReg::imm(((src >> 6) & 0x1f) as i32)),

        0b1001000 | 0b1001001 | 0b1001010 | 0b1001011 =>
            context.str(INST_NORMAL,
                        register(((src >> 8) & 7) as i8),
                        ImmOrReg::Reg(Register::SP),
                        ImmOrReg::imm((src & 0xff) as i32)),
        

        0b1001100 | 0b1001101 | 0b1001110 | 0b1001111 =>
            context.ldr(INST_NORMAL,
                        register(((src >> 8) & 7) as i8),
                        ImmOrReg::Reg(Register::SP),
                        ImmOrReg::imm((src & 0xff) as i32)),

        // ADR
        0b1010000 | 0b1010001 | 0b1010010 | 0b1010011 =>
            context.adr(register(((src >> 8) & 0x7) as i8),
                        ImmOrReg::imm((src & 0xff) as i32)),
        
        // ADD (SP+imm)
        0b1010100 | 0b1010101 | 0b1010110 | 0b1010111 =>
            context.add(INST_NORMAL,
                        register(((src >> 8) & 7) as i8),
                        ImmOrReg::Reg(Register::SP),
                        ImmOrReg::imm((src & 0xff) as i32)),

        // Push/Pop
        0b1011010 => context.stm(INST_NORMAL,
                                 Register::SP,
                                 (0x4000 | (src & 0xff)) as u16,
                                 true),
        0b1011110 => context.ldm(INST_NORMAL,
                                 Register::SP,
                                 (0x4000 | (src & 0xff)) as u16,
                                 true),

        // Misc
        0b1011000 | 0b1011001 | 0b1011011 |
        0b1011100 | 0b1011101 | 0b1011111 => {
            match (src >> 5) & 0x7f {
                0b0110011 => context.cps((src & 0x10) != 0,
                                      (src & 0x02) != 0,
                                      (src & 0x01) != 0),

                0b000000 | 0b000001 | 0b000010 | 0b000011 =>
                    context.add(INST_NORMAL,
                                Register::SP,
                                ImmOrReg::Reg(Register::SP),
                                ImmOrReg::imm((src & 0x7f) as i32)),
                0b000100 | 0b000101 | 0b000110 | 0b000111 =>
                    context.sub(INST_NORMAL,
                                Register::SP,
                                ImmOrReg::Reg(Register::SP),
                                ImmOrReg::imm((src & 0x7f) as i32)),
                
                0b001000 | 0b001001 | 0b001010 | 0b001011 |
                0b001100 | 0b001101 | 0b001110 | 0b001111 =>
                    context.cbz(false,
                                register((src & 3) as i8),
                                ImmOrReg::imm(((src >> 2) & 0x3e) as i32)),

                0b0010000 | 0b0010001 =>
                    context.xt(true,
                               INST_WORD | INST_SIGNED,
                               register((src & 7) as i8),
                               register(((src >> 3) & 7) as i8)),
                
                0b0010010 | 0b0010011 =>
                    context.xt(true,
                               INST_BYTE | INST_SIGNED,
                               register((src & 7) as i8),
                               register(((src >> 3) & 7) as i8)),

                0b0010100 | 0b0010101 =>
                    context.xt(true,
                               INST_WORD,
                               register((src & 7) as i8),
                               register(((src >> 3) & 7) as i8)),
                
                0b0010110 | 0b0010111 =>
                    context.xt(true,
                               INST_BYTE,
                               register((src & 7) as i8),
                               register(((src >> 3) & 7) as i8)),

                0b0011000 | 0b0011001 | 0b0011010 | 0b0011011 |
                0b0011100 | 0b0011101 | 0b0011110 | 0b0011111 =>
                    context.cbz(false,
                                register((src & 3) as i8),
                                ImmOrReg::imm((((src >> 2) & 0x3e) | 0x40) as i32)),

                0b1010000 | 0b1010001 =>
                    context.rev(INST_NORMAL,
                                register((src & 7) as i8),
                                ImmOrReg::register(((src >> 3) & 7) as i8)),

                0b1010010 | 0b1010011 =>
                    context.rev(INST_WORD,
                                register((src & 7) as i8),
                                ImmOrReg::register(((src >> 3) & 7) as i8)),

                0b1010100 | 0b1010101 =>
                    context.rev(INST_WORD | INST_SIGNED,
                                register((src & 7) as i8),
                                ImmOrReg::register(((src >> 3) & 7) as i8)),
                
                0b1001000 | 0b1001001 | 0b1001010 | 0b1001011 |
                0b1001100 | 0b1001101 | 0b1001110 | 0b1001111 =>
                    context.cbz(true,
                                register((src & 3) as i8),
                                ImmOrReg::imm(((src >> 2) & 0x3e) as i32)),

                0b1011000 | 0b1011001 | 0b1011010 | 0b1011011 |
                0b1011100 | 0b1011101 | 0b1011110 | 0b1011111 =>
                    context.cbz(true,
                                register((src & 3) as i8),
                                ImmOrReg::imm((((src >> 2) & 0x3e) | 0x40) as i32)),

                0b1110000 | 0b1110001 | 0b1110010 | 0b1110011 | 
                0b1110100 | 0b1110101 | 0b1110110 | 0b1110111 =>
                    context.bkpt((src & 0xff) as i8),

                0b1111000 | 0b1111001 | 0b1111010 | 0b1111011 |
                0b1111100 | 0b1111101 | 0b1111110 | 0b1111111 => {
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
                            0b0100 => context.sev(),
                            
                            _ => context.nop(),
                        }
                    }
                }
                
                _ => context.undefined(),
            }
            
        },

        // STM

        0b1100000 | 0b1100001 | 0b1100010 | 0b1100011 =>
            context.stm(INST_NORMAL,
                        register(((src >> 8) & 7) as i8),
                        (src & 0xff) as u16,
                        true),

        // LDM
        
        0b1100100 | 0b1100101 | 0b1100110 | 0b1100111 => {
            let reg_idx = (src >> 8) & 7;
            context.ldm(INST_NORMAL,
                        register(reg_idx as i8),
                        (src & 0xff) as u16,
                        (src & (1 << reg_idx)) != 0)
        },

        0b1101000 | 0b1101001 | 0b1101010 | 0b1101011 |
        0b1101100 | 0b1101101 | 0b1101110  => {
            context.b(condition(((src >> 8) & 0xf) as i8),
                      ImmOrReg::imm(((src & 0xff) << 1) as i32),
                      false, false)
        }

        0b1101111 => {
            if (src & 0x10) != 0 {
                context.svc((src & 0xff) as i8)
            } else {
                context.undefined()
            }
        },

        0b1110000 | 0b1110001 | 0b1110010 | 0b1110011 =>
            context.b(Condition::AL,
                      ImmOrReg::imm((((src & 0x3ff) << 2) as i32) >> 1),
                      false, false),
        
        _ => context.undefined(),
    }

    Ok(())
}

pub fn execute_32<T: ExecutionContext>(src: u32, context: &mut T) -> Result<()> {
    Err(Error::Unknown)
}

