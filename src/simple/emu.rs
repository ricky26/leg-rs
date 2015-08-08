use std::fmt;
use std::fmt::Write;

use super::{System, Memory};
use super::super::*;
use super::super::{register, bits};

/// A convenience wrapper for the CPSR.
#[derive(Copy,Clone)]
pub struct CPSR(pub u32);

impl CPSR {
    /// Create an empty CPSR.
    pub fn new() -> CPSR { CPSR(0) }
    
    /// Create a modified CPSR value with the given mask bits
    /// set to those in the value field.
    pub fn with_bits(&self, mask: u32, value: u32) -> CPSR { CPSR((self.0 &! mask) | (value & mask)) }
    
    /// value bit.
    pub fn negative(&self) -> bool { bits(self.0, 31, 1) != 0 }
    /// Create a new CPSR with value bit value.
    pub fn with_negative(&self, value: bool) -> CPSR { self.with_bits(1 << 31, (value as u32) << 31) }

    /// Z bit.
    pub fn zero(&self) -> bool { bits(self.0, 30, 1) != 0 }
    /// Create a new CPSR with Z bit value.
    pub fn with_zero(&self, value: bool) -> CPSR { self.with_bits(1 << 30, (value as u32) << 30) }

    /// C bit.
    pub fn carry(&self) -> bool { bits(self.0, 29, 1) != 0 }
    /// Create a new CPSR with C bit value.
    pub fn with_carry(&self, value: bool) -> CPSR { self.with_bits(1 << 29, (value as u32) << 29) }

    /// V bit.
    pub fn overflow(&self) -> bool { bits(self.0, 28, 1) != 0 }
    /// Create a new CPSR with V bit value.
    pub fn with_overflow(&self, value: bool) -> CPSR { self.with_bits(1 << 28, (value as u32) << 28) }

    /// Q bit.
    pub fn saturated(&self) -> bool { bits(self.0, 27, 1) != 0 }
    /// Create a new CPSR with V bit value.
    pub fn with_saturated(&self, value: bool) -> CPSR { self.with_bits(1 << 27, (value as u32) << 27) }

    /// THUMB-mode bit.
    pub fn thumb(&self) -> bool { bits(self.0, 5, 1) != 0 }
    /// New CPSR with THUMB mode bit.
    pub fn with_thumb(&self, value: bool) -> CPSR { self.with_bits(1 << 5, (value as u32) << 5) }
}

impl fmt::Debug for CPSR {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        write!(fmt, "0x{:08x} {{{}{}{}{}{}}}",
               self.0,
               if self.negative()  { "N" } else { "-" },
               if self.zero()      { "Z" } else { "-" },
               if self.carry()     { "V" } else { "-" },
               if self.overflow()  { "C" } else { "-" },
               if self.saturated() { "Q" } else { "-" })
    }
}

pub struct SimpleEmulator<S: System> {
    pub system: S,
    
    registers: [Word;16],
    cpsr: CPSR,
    itt_mask: u8,
    itt_count: i8,
    itt_cond: Condition,
    paused: bool,
    next_pc: Word,
    inst_size: Word,
    debugging: bool,
    
    pending_gdb_commands: Vec<gdb::Command<'static>>,
}

impl<S: System> SimpleEmulator<S> {
    pub fn new(system: S) -> SimpleEmulator<S> {
        SimpleEmulator {
            registers: [0i32;16],
            cpsr: CPSR::new().with_thumb(true),
            system: system,
            itt_mask: 0u8,
            itt_count: 0,
            itt_cond: Condition::AL,
            paused: false,
            next_pc: 0i32,
            inst_size: 0i32,
            debugging: false,

            pending_gdb_commands: Vec::new(),
        }
    }

    pub fn memory_mut(&mut self) -> &mut S::Memory {
        self.system.memory_mut()
    }

    pub fn debugging(&self) -> bool { self.debugging }
    pub fn start_debugging(&mut self) { self.debugging = true; }

    pub fn register(&self, reg: Register) -> Word {
        self.registers[reg.index() as usize]
    }

    pub fn set_register(&mut self, reg: Register, value: Word) {
        self.registers[reg.index() as usize] = value
    }

    pub fn cpu_register(&self, flags: InstructionFlags, reg: Register) -> Word {
        if reg == Register::PC {
            let mut val = self.register(Register::PC) + 4;

            if flags.get(INST_ALIGN) {
                val = val &! 0b11;
            }

            val
        } else {
            self.register(reg)
        }
    }

    pub fn cpu_set_register(&mut self, _flags: InstructionFlags, reg: Register, value: Word) {
        if reg == Register::PC {
            self.next_pc = value;
        } else {
            self.set_register(reg, value);
        }
    }

    pub fn imm_or_reg<T: IntTruncate>(&self, flags: InstructionFlags, imm_or_reg: ImmOrReg<T>) -> T {
        match imm_or_reg {
            ImmOrReg::Reg(x) => T::int_truncate(self.cpu_register(flags, x)),
            ImmOrReg::Imm(x) => x,
        }
    }

    pub fn shift(&self, flags: InstructionFlags, src: Word, shift: Shift) -> (Word, bool) {
        let topbit = 0x80000000u32 as i32;
        
        match (shift.0, self.imm_or_reg(flags, shift.1)) {
            (ShiftType::None, _) => (src, false),
            (ShiftType::LSL, x) => (src << x, ((src << (x-1)) & topbit) != 0),
            (ShiftType::LSR, x) => {
                let result = ((src as u32) >> (x as u32)) as Word;
                let extra = ((src as u32) >> ((x-1) as u32)) as Word;
                (result, (extra & 1) != 0)
            },
            (ShiftType::ASR, x) => {
                let result = src >> x;
                let extra = src >> (x-1);
                (result, (extra & 1) != 0)
            },
            (ShiftType::ROR, x) => {
                let src = src as u32;
                let shift = x as u32;
                let result = ((src >> shift) | (src << (32-shift))) as Word;
                (result, (result & topbit) != 0)
            },
            _ => panic!("TODO: unimplemented shift type"),
        }
    }

    pub fn shifted(&self, flags: InstructionFlags, src: Shifted) -> (Word, bool) {
        self.shift(flags, self.imm_or_reg(flags, src.1), src.0)
    }

    pub fn should_set_flags(&self, flags: InstructionFlags) -> bool {
        flags.get(INST_SET_FLAGS) && (self.itt_count == 0)
    }

    pub fn cpsr(&self) -> CPSR { self.cpsr.clone() }
    pub fn set_cpsr(&mut self, cpsr: CPSR) {
        self.cpsr = cpsr;
    }
    
    pub fn set_cpsr_from_value(&mut self, result: Word) {
        let cpsr = self.cpsr.with_negative((result & (1 << 31)) != 0)
            .with_zero(result == 0);
        self.set_cpsr(cpsr);
    }

    pub fn set_cpsr_from_add(&mut self, result: Word, carry: bool, overflow: bool) {
        let cpsr = self.cpsr.with_negative((result & (1 << 31)) != 0)
            .with_zero(result == 0)
            .with_carry(carry)
            .with_overflow(overflow);
        self.set_cpsr(cpsr)
    }

    pub fn cond(&self, cond: Condition) -> bool {
        match cond {
            Condition::EQ => self.cpsr.zero(),
            Condition::NE => !self.cpsr.zero(),
            Condition::CS => self.cpsr.carry(),
            Condition::CC => !self.cpsr.carry(),
            Condition::MI => self.cpsr.negative(),
            Condition::PL => !self.cpsr.negative(),
            Condition::VS => self.cpsr.overflow(),
            Condition::VC => !self.cpsr.overflow(),
            Condition::HI => self.cpsr.carry() && !self.cpsr.zero(),
            Condition::LS => !self.cpsr.carry() && self.cpsr.zero(),
            Condition::GE => self.cpsr.negative() == self.cpsr.overflow(),
            Condition::LT => self.cpsr.negative() != self.cpsr.overflow(),
            Condition::GT => !self.cpsr.zero() && (self.cpsr.negative() == self.cpsr.overflow()),
            Condition::LE => self.cpsr.zero() || (self.cpsr.negative() != self.cpsr.overflow()),
            Condition::AL => true,
        }
    }

    pub fn branch(&mut self, flags: InstructionFlags, addr: i32) -> Result<()> {
        if flags.get(INST_LINK) {
            let pc = self.register(Register::PC) + self.inst_size;
            self.cpu_set_register(flags, Register::LR, pc);
        }

        if flags.get(INST_EXCHANGE) {
            // TODO: Check whether we need to swap between ARM/THUMB
        }

        if flags.get(INST_JAZELLE) {
            // TODO: Jazelle!
        }

        self.cpu_set_register(flags, Register::PC, addr);

        Ok(())
    }

    pub fn execute_one(&mut self) -> Result<()> {
        if self.paused { return Ok(()) }
        
        let mut buf = [0u8; 4];
        let mut pc = self.register(Register::PC);

        // TODO: ARM vs THUMB mode

        try!(self.memory_mut().read(pc as u64, &mut buf[..2]));
        pc += 2;
        self.inst_size = 2;

        let is_32bit = thumb::is_32bit(&buf);

        if is_32bit {
            try!(self.memory_mut().read(pc as u64, &mut buf[2..4]));
            pc += 2;
            self.inst_size = 4;
        }

        self.next_pc = pc;

        if self.itt_count > 0 {
            let skip = ((self.itt_mask & 1) != 0) ^ self.cond(self.itt_cond);
            self.itt_mask >>= 1;
            self.itt_count -= 1;

            if skip {
                return Ok(())
            }
        }

        match thumb::execute(self, if is_32bit { &mut buf } else { &mut buf[..2] }) {
            (_, Err(x)) => { return Err(x) },
            _ => {},
        }
        pc = self.next_pc;
        self.set_register(Register::PC, pc);
        Ok(())
    }

    pub fn execute(&mut self) -> Result<()> {
        loop {
            try!(self.execute_one());
        }
    }

    pub fn dump_state(&self, fmt: &mut fmt::Write) -> fmt::Result {
        try!(writeln!(fmt, "processor state:"));
        try!(writeln!(fmt, "\tcpsr: {:?}", self.cpsr));
        try!(writeln!(fmt, "\tregisters:"));
        for reg in &[Register::R0,
                     Register::R1,
                     Register::R2,
                     Register::R3,
                     Register::R4,
                     Register::R5,
                     Register::R6,
                     Register::R7,
                     Register::R8,
                     Register::R9,
                     Register::R10,
                     Register::R11,
                     Register::R12,
                     Register::SP,
                     Register::LR,
                     Register::PC] {

            try!(writeln!(fmt, "\t\t{}\t= 0x{:08x}", reg, self.register(*reg)));
        }

        Ok(())
    }

    pub fn print_state(&self) -> Result<()> {
        let mut out = String::new();
        try!(self.dump_state(&mut out));
        println!("{}", out);
        Ok(())
    }

    pub fn set_paused(&mut self, paused: bool) {
        self.paused = paused;
    }

    pub fn send_gdb_command<'a>(&mut self, cmd: &gdb::Command<'a>) {
        self.pending_gdb_commands.push(cmd.to_owned());
    }

    pub fn with_pending_gdb_commands<T: for<'a> FnMut(&'a gdb::Command<'a>)>(&mut self, mut callback: T) {
        for i in self.pending_gdb_commands.iter() {
            callback(&i);
        }
        self.pending_gdb_commands.clear()
    }

    pub fn process_gdb_command(&mut self, cmd: &gdb::Command) {
        self.debugging = true;
        
        if cmd.contents() == "?" {
            if self.paused {
                self.send_gdb_command(&gdb::Command::new("S05"));
            } else {
                self.send_gdb_command(&gdb::Command::new("S13"));
            }
        } else if cmd.contents() == "g" {

            let mut out = String::new();
            for i in 0..16 {
                write!(&mut out, "{:08x}", super::swap_word(self.registers[i])).unwrap();
            }

            for _ in 0..8 {
                write!(&mut out, "{:016x}", 0x12345678abcdefu64).unwrap();
            }

            write!(&mut out, "{:08x}", 0x12345678u32).unwrap();
            write!(&mut out, "{:08x}", super::swap_word(self.cpsr.0 as i32)).unwrap();

            self.send_gdb_command(&gdb::Command::new_owned(out));
        } else if cmd.contents() == "c" {
            self.paused = false;
        } else if cmd.contents() == "s" {
            let paws = self.paused;
            self.paused = false;
            match self.execute_one() {
                Err(x) => println!("ERROR: {:?}", x),
                _ => {},
            }
            self.paused = paws;
            self.send_gdb_command(&gdb::Command::new("S05"));
        } else if let Some(caps) = regex!("p([0-9a-fA-F]+)").captures(cmd.contents()) {
            let reg = usize::from_str_radix(caps.at(1).unwrap(), 16).unwrap();

            let mut out = String::new();
            match reg {
                0...15 => write!(&mut out, "{:08x}", super::swap_word(self.registers[reg])).unwrap(),
                16...23 => write!(&mut out, "{:016x}", 0x12345678abcdefu64).unwrap(),
                25 => write!(&mut out, "{:08x}", super::swap_word(self.cpsr.0 as i32)).unwrap(),
                _ => write!(&mut out, "{:08x}", 0i32).unwrap(),
            };
            
            self.send_gdb_command(&gdb::Command::new_owned(out));
        } else if let Some(caps) = regex!("m([0-9a-fA-F]+),([0-9a-fA-F]+)").captures(cmd.contents()) {
            let start = u64::from_str_radix(caps.at(1).unwrap(), 16).unwrap();
            let len = usize::from_str_radix(caps.at(2).unwrap(), 16).unwrap();

            let mut vec = Vec::new();
            vec.reserve(len);
            //unsafe { vec.set_len(len); }

            for _ in 0..len {
                vec.push(0u8);
            }
            
            self.memory_mut().read(start, &mut vec[..]).ok();

            let mut out = String::new();
            for i in vec {
                write!(&mut out, "{:02x}", i).unwrap();
            }

            self.send_gdb_command(&gdb::Command::new_owned(out));
        } else if let Some(caps) = regex!("M([0-9a-fA-F]+),([0-9a-fA-F]+):([0-9a-fA-F]+)").captures(cmd.contents()) {
            let start = u64::from_str_radix(caps.at(1).unwrap(), 16).unwrap();
            let len = usize::from_str_radix(caps.at(2).unwrap(), 16).unwrap();
            let hex = caps.at(3).unwrap();

            for i in 0..len {
                let buf = [u8::from_str_radix(&hex[i*2..(i+1)*2], 16).unwrap()];
                self.memory_mut().write(start+(i as u64), &buf).ok();
            }

            self.send_gdb_command(&gdb::Command::new("OK"));
        } else {
            println!("Unimplemented GDB command: {}", cmd.contents());
            self.send_gdb_command(&gdb::Command::new(""));
        }
    }
}


impl<'a, S: System> ExecutionContext for SimpleEmulator<S> {
    fn undefined(&mut self, msg: &str) -> Result<()> {
        if !self.debugging {
            Err(Error::Unknown(format!("undefined {} @ {}", msg, self.register(Register::PC))))
        } else {
            Err(Error::Undefined("bkpt".into()))
        }
    }
    fn unpredictable(&mut self) -> Result<()> {
        if !self.debugging {
            Err(Error::Unknown(format!("unpredictable @ {}", self.register(Register::PC))))
        } else {
            self.undefined("")
        }
    }
    
    // Move
    fn mov(&mut self, flags: InstructionFlags, dest: Register, src: Shifted) -> Result<()> {
        let (val, _c) = self.shifted(flags, src);
        if self.should_set_flags(flags) {
            self.set_cpsr_from_value(val);
        }
        self.cpu_set_register(flags, dest, val);
        Ok(())
    }
    
    // Add/subtract
    fn add(&mut self, flags: InstructionFlags, dest: Register, src: ImmOrReg<Word>, add: Shifted) -> Result<()> {
        let a = self.imm_or_reg(flags, src);
        let (b, _c) = self.shifted(flags, add);
        let (result, carry, overflow) = super::adc32(a, b, 0);
        
        if self.should_set_flags(flags) {
            self.set_cpsr_from_add(result, carry, overflow);
        }
        self.cpu_set_register(flags, dest, result);
        Ok(())
    }
    fn sub(&mut self, flags: InstructionFlags, dest: Register, src: ImmOrReg<Word>, sub: Shifted) -> Result<()> {
        let a = self.imm_or_reg(flags, src);
        let (b, _c) = self.shifted(flags, sub);
        let (result, carry, overflow) = super::adc32(a, !b, 1);

        if self.should_set_flags(flags) {
            self.set_cpsr_from_add(result, carry, overflow);
        }
        self.cpu_set_register(flags, dest, result);
        Ok(())
    }
    fn rsb(&mut self, flags: InstructionFlags, dest: Register, src: ImmOrReg<Word>, sub: Shifted) -> Result<()> {
        let a = self.imm_or_reg(flags, src);
        let (b, _c) = self.shifted(flags, sub);
        let (result, carry, overflow) = super::adc32(!a, b, 1);
        
        if self.should_set_flags(flags) {
            self.set_cpsr_from_add(result, carry, overflow);
        }
        self.cpu_set_register(flags, dest, result);
        Ok(())
    }
    fn adc(&mut self, flags: InstructionFlags, dest: Register, src: ImmOrReg<Word>, add: Shifted) -> Result<()> {
        let a = self.imm_or_reg(flags, src);
        let (b, _c) = self.shifted(flags, add);
        let (result, carry, overflow) = super::adc32(a, b, self.cpsr.carry() as Word);

        if self.should_set_flags(flags) {
            self.set_cpsr_from_add(result, carry, overflow);
        }
        self.cpu_set_register(flags, dest, result);
        Ok(())
    }
    fn sbc(&mut self, flags: InstructionFlags, dest: Register, src: ImmOrReg<Word>, sub: Shifted) -> Result<()> {
        let a = self.imm_or_reg(flags, src);
        let (b, _c) = self.shifted(flags, sub);
        let (result, carry, overflow) = super::adc32(a, !b, self.cpsr.carry() as Word);
        
        if self.should_set_flags(flags) {
            self.set_cpsr_from_add(result, carry, overflow);
        }
        self.cpu_set_register(flags, dest, result);
        Ok(())
    }
    fn cmp(&mut self, flags: InstructionFlags, a: Register, b: Shifted) -> Result<()> {
        let a = self.cpu_register(flags, a);
        let (b, _c) = self.shifted(flags, b);
        let (result, carry, overflow) = super::adc32(a, !b, 1);
        self.set_cpsr_from_add(result, carry, overflow);
        Ok(())
    }
    fn cmn(&mut self, flags: InstructionFlags, a: Register, b: Shifted) -> Result<()> {
        let a = self.cpu_register(flags, a);
        let (b, _c) = self.shifted(flags, b);
        let (result, carry, overflow) = super::adc32(a, b, 0);
        self.set_cpsr_from_add(result, carry, overflow);
        Ok(())
    }
    
    // Bitwise
    fn and(&mut self, flags: InstructionFlags, dest: Register, src: ImmOrReg<Word>, operand: Shifted) -> Result<()> {
        let (operand, carry) = self.shifted(flags, operand);
        let val = self.imm_or_reg(flags, src) & operand;
        self.cpu_set_register(flags, dest, val);
        if self.should_set_flags(flags) {
            let cpsr = self.cpsr
                .with_negative((val & (1 << 31)) != 0)
                .with_zero(val == 0)
                .with_carry(carry);
            self.set_cpsr(cpsr);
        }
        Ok(())
    }
    fn orr(&mut self, flags: InstructionFlags, dest: Register, src: ImmOrReg<Word>, operand: Shifted) -> Result<()> {
        let (operand, carry) = self.shifted(flags, operand);
        let val = self.imm_or_reg(flags, src) | operand;
        self.cpu_set_register(flags, dest, val);
        if self.should_set_flags(flags) {
            let cpsr = self.cpsr
                .with_negative((val & (1 << 31)) != 0)
                .with_zero(val == 0)
                .with_carry(carry);
            self.set_cpsr(cpsr);
        }
        Ok(())
    }
    fn eor(&mut self, flags: InstructionFlags, dest: Register, src: ImmOrReg<Word>, operand: Shifted) -> Result<()> {
        let (operand, carry) = self.shifted(flags, operand);
        let val = self.imm_or_reg(flags, src) ^ operand;
        self.cpu_set_register(flags, dest, val);
        if self.should_set_flags(flags) {
            let cpsr = self.cpsr
                .with_negative((val & (1 << 31)) != 0)
                .with_zero(val == 0)
                .with_carry(carry);
            self.set_cpsr(cpsr);
        }
        Ok(())
    }

    fn mvn(&mut self, flags: InstructionFlags, dest: Register, operand: Shifted) -> Result<()> {
        let (operand, carry) = self.shifted(flags, operand);
        let val = !operand;
        self.cpu_set_register(flags, dest, val);
        if self.should_set_flags(flags) {
            let cpsr = self.cpsr
                .with_negative((val & (1 << 31)) != 0)
                .with_zero(val == 0)
                .with_carry(carry);
            self.set_cpsr(cpsr);
        }
        Ok(())
    }
    
    fn str(&mut self, flags: InstructionFlags, src: Register, dest: ImmOrReg<Word>, off: Shifted) -> Result<()> {
        let base = self.imm_or_reg(flags, dest);
        let (operand, _c) = self.shifted(flags, off);
        let addr = base + operand;
        let value = self.cpu_register(flags, src);
        
        if flags.get(INST_BYTE) {
            self.memory_mut().write_u8(addr as u64, value as u8)
        } else if flags.get(INST_HALF) {
            self.memory_mut().write_u16(addr as u64, value as u16)
        } else {
            self.memory_mut().write_u32(addr as u64, value as u32)
        }
    }
    
    fn ldr(&mut self, flags: InstructionFlags, dest: Option<Register>, src: ImmOrReg<Word>, off: Shifted) -> Result<()> {        
        let base = self.imm_or_reg(flags, src);
        let (operand, _c) = self.shifted(flags, off);
        let addr = base + operand;
        let value;
        
        if flags.get(INST_BYTE) {
            value = try!(self.memory_mut().read_u8(addr as u64)) as i32;
        } else if flags.get(INST_HALF) {
            value = try!(self.memory_mut().read_u16(addr as u64)) as i32;
        } else {
            value = try!(self.memory_mut().read_u32(addr as u64)) as i32;
        }

        if let Some(dest) = dest {
            self.cpu_set_register(flags, dest, value);
        }
        
        Ok(())
    }
    
    fn ldm(&mut self, flags: InstructionFlags, dest: Register, registers: u16) -> Result<()> {
        let mut addr = self.cpu_register(flags, dest);
        let writeback = flags.get(INST_WRITEBACK);
        let dec = flags.get(INST_DECREMENT);
        let before = flags.get(INST_BEFORE);
        
        for i in 0..16 {
            let i = if dec { 15-i } else { i };
            if (registers & (1 << i)) == 0 { continue }
            let reg = register(i);
            
            if reg == dest { continue }

            if before {
                if dec {
                    addr -= 4
                } else {
                    addr += 4
                }
            }

            if let Ok(value) = self.memory_mut().read_u32(addr as u64) {
                self.cpu_set_register(flags, reg, value as i32);
            }
            
            if !before {
                if dec {
                    addr -= 4
                } else {
                    addr += 4
                }
            }
        }

        if writeback {
            self.cpu_set_register(flags, dest, addr)
        }

        Ok(())
    }
    
    fn stm(&mut self, flags: InstructionFlags, dest: Register, registers: u16) -> Result<()> {
        let mut addr = self.cpu_register(flags, dest);
        let writeback = flags.get(INST_WRITEBACK);
        let dec = flags.get(INST_DECREMENT);
        let before = flags.get(INST_BEFORE);

        for i in 0..16 {
            let i = if dec { 15-i } else { i };
            if (registers & (1 << i)) == 0 { continue }
            let reg = register(i);
            if reg == dest { continue }

            if before {
                if dec {
                    addr -= 4
                } else {
                    addr += 4
                }
            }

            let value = self.cpu_register(flags, reg);
            self.memory_mut().write_u32(addr as u64, value as u32).ok();
            
            if !before {
                if dec {
                    addr -= 4
                } else {
                    addr += 4
                }
            }
        }

        if writeback {
            self.cpu_set_register(flags, dest, addr)
        }
        
        Ok(())
    }

    fn b(&mut self, flags: InstructionFlags, cond: Condition, base: Register, addr: ImmOrReg<Word>) -> Result<()> {
        if !self.cond(cond) {
            return Ok(())
        }

        let base = self.cpu_register(flags, base);
        let addr = base + self.imm_or_reg(flags, addr);

        self.branch(flags, addr)
    }
    
    fn cbz(&mut self, flags: InstructionFlags, src: Register, base: Register, addr: ImmOrReg<Word>) -> Result<()> {
        let src = self.cpu_register(flags, src);
        let cond = if flags.get(INST_NONZERO) { src != 0 } else { src == 0 };

        if cond {
            let base = self.cpu_register(flags, base);
            let addr = base + self.imm_or_reg(flags, addr);
            self.branch(flags, addr)
        } else {
            Ok(())
        }
    }
}
