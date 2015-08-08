use std::fmt;

use super::*;
use super::register;
use std::fmt::Write;

pub trait IntTruncate {
    fn int_truncate(src: Word) -> Self;
}

impl IntTruncate for i64 {
    fn int_truncate(src: Word) -> i64 { src as i64 }
}

impl IntTruncate for i32 {
    fn int_truncate(src: Word) -> i32 { src as i32 }
}

impl IntTruncate for i16 {
    fn int_truncate(src: Word) -> i16 { src as i16 }
}

impl IntTruncate for i8 {
    fn int_truncate(src: Word) -> i8 { src as i8 }
}

fn swap_word(src: Word) -> Word {
    let src = src as u32;
    let src = (src >> 24)
        | ((src >> 8) & 0xff00)
        | ((src << 8) & 0xff0000)
        | ((src << 24) & 0xff000000);
    src as Word
}

pub trait Memory {
    fn read(&self, addr: u64, dest: &mut [u8]) -> Result<()>;
    fn write(&mut self, addr: u64, src: &[u8]) -> Result<()>;

    fn read_u8(&self, addr: u64) -> Result<u8> {
        let mut data = [0u8];
        try!(self.read(addr, &mut data));
        Ok(data[0])
    }

    fn read_u16(&self, addr: u64) -> Result<u16> {
        let mut data = [0u8;2];
        try!(self.read(addr, &mut data));
        Ok((data[0] as u16) | ((data[1] as u16) << 8))
    }

    fn read_u32(&self, addr: u64) -> Result<u32> {
        let mut data = [0u8;4];
        try!(self.read(addr, &mut data));
        Ok((data[0] as u32)
           | ((data[1] as u32) << 8)
           | ((data[2] as u32) << 16)
           | ((data[3] as u32) << 24))
    }

    fn write_u8(&mut self, addr: u64, val: u8) -> Result<()> {
        self.write(addr, &[val])
    }

    fn write_u16(&mut self, addr: u64, val: u16) -> Result<()> {
        self.write(addr, &[(val & 0xff) as u8,
                           ((val >> 8) & 0xff) as u8])
    }

    fn write_u32(&mut self, addr: u64, val: u32) -> Result<()> {
        self.write(addr, &[(val & 0xff) as u8,
                           ((val >> 8) & 0xff) as u8,
                           ((val >> 16) & 0xff) as u8,
                           ((val >> 24) & 0xff) as u8])
    }
}

pub struct SimpleEmulator<M: Memory> {
    pub memory: M,
    
    registers: [Word;16],
    apsr: u32,
    itt_mask: u8,
    itt_count: i8,
    itt_cond: Condition,
    paused: bool,
    next_pc: Word,
    inst_size: Word,
    
    pending_gdb_commands: Vec<gdb::Command<'static>>,
}

impl<M: Memory> SimpleEmulator<M> {
    pub fn new(memory: M) -> SimpleEmulator<M> {
        SimpleEmulator {
            registers: [0i32;16],
            apsr: 0u32,
            memory: memory,
            itt_mask: 0u8,
            itt_count: 0,
            itt_cond: Condition::AL,
            paused: false,
            next_pc: 0i32,
            inst_size: 0i32,

            pending_gdb_commands: Vec::new(),
        }
    }

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

    pub fn shift(&self, flags: InstructionFlags, src: Word, shift: Shift) -> Word {
        match (shift.0, self.imm_or_reg(flags, shift.1)) {
            (ShiftType::None, _) => src,
            (ShiftType::LSL, x) => src << x,
            (ShiftType::LSR, x) => ((src as u32) << (x as u32)) as Word,
            (ShiftType::ASR, x) => src >> x,
            (ShiftType::ROR, x) => {
                let src = src as u32;
                let shift = x as u32;
                ((src >> shift) | (src << (32-shift))) as Word
            },
            _ => panic!("TODO: unimplemented shift type"),
        }
    }

    pub fn shifted(&self, flags: InstructionFlags, src: Shifted) -> Word {
        self.shift(flags, self.imm_or_reg(flags, src.1), src.0)
    }
    
    pub fn negative(&self) -> bool {
        ((self.apsr >> 31) & 1) != 0
    }

    pub fn zero(&self) -> bool {
        ((self.apsr >> 30) & 1) != 0
    }

    pub fn carry(&self) -> bool {
        ((self.apsr >> 29) & 1) != 0
    }
    
    pub fn overflow(&self) -> bool {
        ((self.apsr >> 28) & 1) != 0
    }
    
    pub fn saturated(&self) -> bool {
        ((self.apsr >> 27) & 1) != 0
    }

    pub fn set_apsr(&mut self, apsr: u32) {
        self.apsr = apsr
    }

    pub fn cond(&self, cond: Condition) -> bool {
        match cond {
            Condition::EQ => self.zero(),
            Condition::NE => !self.zero(),
            Condition::CS => self.carry(),
            Condition::CC => !self.carry(),
            Condition::MI => self.negative(),
            Condition::PL => !self.negative(),
            Condition::VS => self.overflow(),
            Condition::VC => !self.overflow(),
            Condition::HI => self.carry() && !self.zero(),
            Condition::LS => !self.carry() && self.zero(),
            Condition::GE => self.negative() == self.overflow(),
            Condition::LT => self.negative() != self.overflow(),
            Condition::GT => !self.zero() && (self.negative() == self.overflow()),
            Condition::LE => self.zero() || (self.negative() != self.overflow()),
            Condition::AL => true,
        }
    }

    pub fn cmp(&mut self, a: Word, b: Word, c: Word) {
        let ua = a as u32;
        let ub = b as u32;
        let uc = c as u32;
        
        let mut apsr = ua.wrapping_sub(ub).wrapping_sub(uc) & 0x80000000;
        
        if ua == ub {
            apsr |= 1u32 << 30
        }
        if ua > ub {
            apsr |= 1u32 << 29
        }
        if ((a < 0) && (b > (2147483647i32.wrapping_sub(a).wrapping_add(1))))
            || ((a > 0) && (-b > (a.wrapping_sub(2147483647)))) {
                apsr |= 1u32 << 28
            }

        self.set_apsr(apsr)
    }

    pub fn cmn(&mut self, a: Word, b: Word, c: Word) {
        let ua = a as u32;
        let ub = b as u32;
        let uc = c as u32;
        
        let mut apsr = ua.wrapping_add(ub).wrapping_add(uc) & 0x80000000;
        
        if (ua + ub) == 0 {
            apsr |= 1u32 << 30
        }
        if (4294967295u32 - ua) > ub {
            apsr |= 1u32 << 29
        }
        if ((a < 0) && (b < -(2147483647i32.wrapping_sub(a).wrapping_add(1))))
            || ((a > 0) && (b > (a.wrapping_sub(2147483647)))) {
                apsr |= 1u32 << 28
            }

        self.set_apsr(apsr)
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

    pub fn current_instruction(&self) -> Result<Word> {
        let mut buf = [0u8; 4];
        let pc = self.register(Register::PC);

        // TODO: ARM vs THUMB mode

        try!(self.memory.read(pc as u64, &mut buf[..2]));

        if thumb::is_32bit(&buf) {
            try!(self.memory.read((pc + 2) as u64, &mut buf[2..4]));
        }

        Ok((((buf[0] as Word) << 24)
            | ((buf[1] as Word) << 16)
            | ((buf[2] as Word) << 8)
            | (buf[3] as Word)))
    }
    
    pub fn execute_one(&mut self) -> Result<()> {
        if self.paused { return Ok(()) }
        
        let mut buf = [0u8; 4];
        let mut pc = self.register(Register::PC);

        // TODO: ARM vs THUMB mode

        try!(self.memory.read(pc as u64, &mut buf[..2]));
        pc += 2;
        self.inst_size = 2;

        let is_32bit = thumb::is_32bit(&buf);

        if is_32bit {
            try!(self.memory.read(pc as u64, &mut buf[2..4]));
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

        let (_, err) = super::thumb::execute(self, if is_32bit { &mut buf } else { &mut buf[..2] });
        pc = self.next_pc;
        self.set_register(Register::PC, pc);
        err
    }

    pub fn execute(&mut self) -> Result<()> {
        loop {
            try!(self.execute_one());
        }
    }

    pub fn dump_state(&self, fmt: &mut fmt::Write) -> fmt::Result {
        try!(writeln!(fmt, "registers:"));
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

            try!(writeln!(fmt, "\t{} = 0x{:x}", reg, self.register(*reg)));
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
        if cmd.contents() == "?" {
            if self.paused {
                self.send_gdb_command(&gdb::Command::new("S05"));
            } else {
                self.send_gdb_command(&gdb::Command::new("S13"));
            }
        } else if cmd.contents() == "g" {

            let mut out = String::new();
            for i in 0..16 {
                write!(&mut out, "{:08x}", swap_word(self.registers[i])).unwrap();
            }

            for _ in 0..8 {
                write!(&mut out, "{:016x}", 0x12345678abcdefu64).unwrap();
            }

            write!(&mut out, "{:08x}", 0x12345678u32).unwrap();
            write!(&mut out, "{:08x}", swap_word(self.apsr as i32)).unwrap();

            self.send_gdb_command(&gdb::Command::new_owned(out));
        } else if cmd.contents() == "c" {
            self.paused = false;
        } else if cmd.contents() == "s" {
            let paws = self.paused;
            self.paused = false;
            self.execute_one().ok();
            self.paused = paws;
            self.send_gdb_command(&gdb::Command::new("S05"));
        } else if let Some(caps) = regex!("p([0-9a-fA-F]+)").captures(cmd.contents()) {
            let reg = usize::from_str_radix(caps.at(1).unwrap(), 16).unwrap();

            let mut out = String::new();
            match reg {
                0...15 => write!(&mut out, "{:08x}", swap_word(self.registers[reg])).unwrap(),
                16...23 => write!(&mut out, "{:016x}", 0x12345678abcdefu64).unwrap(),
                25 => write!(&mut out, "{:08x}", swap_word(self.apsr as i32)).unwrap(),
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
            
            self.memory.read(start, &mut vec[..]).ok();

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
                self.memory.write(start+(i as u64), &buf).ok();
            }

            self.send_gdb_command(&gdb::Command::new("OK"));
        } else {
            println!("Unimplemented GDB command: {}", cmd.contents());
            self.send_gdb_command(&gdb::Command::new(""));
        }
    }
}


impl<'a, M: Memory> ExecutionContext for SimpleEmulator<M> {
    fn undefined(&mut self, msg: &str) -> Result<()> {
        println!("PC => {:b}", self.current_instruction().unwrap());
        panic!("undefined {} @ {}", msg, self.register(Register::PC))
    }
    fn unpredictable(&mut self) -> Result<()> {
        println!("PC => {:b}", self.current_instruction().unwrap());
        panic!("unpredictable @ {}", self.register(Register::PC))
    }
    
    // Move
    fn mov(&mut self, flags: InstructionFlags, dest: Register, src: Shifted) -> Result<()> {
        let val = self.shifted(flags, src);
        if (self.itt_count == 0) && ((flags & INST_SET_FLAGS) != INST_NORMAL) {
            self.cmn(val, 0, 0)
        }
        self.cpu_set_register(flags, dest, val);
        Ok(())
    }
    
    // Add/subtract
    fn add(&mut self, flags: InstructionFlags, dest: Register, src: ImmOrReg<Word>, add: Shifted) -> Result<()> {
        let a = self.imm_or_reg(flags, src);
        let b = self.shifted(flags, add);
        let val = a + b;
        
        if (self.itt_count == 0) && ((flags & INST_SET_FLAGS) != INST_NORMAL) {
            self.cmn(a, b, 0)
        }
        self.cpu_set_register(flags, dest, val);
        Ok(())
    }
    fn sub(&mut self, flags: InstructionFlags, dest: Register, src: ImmOrReg<Word>, sub: Shifted) -> Result<()> {
        let a = self.imm_or_reg(flags, src);
        let b = self.shifted(flags, sub);
        let val = a - b;

        if (self.itt_count == 0) && ((flags & INST_SET_FLAGS) != INST_NORMAL) {
            self.cmp(a, b, 0)
        }
        self.cpu_set_register(flags, dest, val);
        Ok(())
    }
    fn rsb(&mut self, flags: InstructionFlags, dest: Register, src: ImmOrReg<Word>, sub: Shifted) -> Result<()> {
        let a = self.imm_or_reg(flags, src);
        let b = self.shifted(flags, sub);
        let val = b - a;
        if (self.itt_count == 0) && ((flags & INST_SET_FLAGS) != INST_NORMAL) {
            self.cmp(b, a, 0)
        }
        self.cpu_set_register(flags, dest, val);
        Ok(())
    }
    fn adc(&mut self, flags: InstructionFlags, dest: Register, src: ImmOrReg<Word>, add: Shifted) -> Result<()> {
        let a = self.imm_or_reg(flags, src);
        let b = self.shifted(flags, add);
        let c = self.carry() as Word;
        let val = a + b + c;
        if (self.itt_count == 0) && ((flags & INST_SET_FLAGS) != INST_NORMAL) {
            self.cmn(a, b, c)
        }
        self.cpu_set_register(flags, dest, val);
        Ok(())
    }
    fn sbc(&mut self, flags: InstructionFlags, dest: Register, src: ImmOrReg<Word>, sub: Shifted) -> Result<()> {
        let a = self.imm_or_reg(flags, src);
        let b = self.shifted(flags, sub);
        let c = self.carry() as Word;
        let val = a - b - c;
        if (self.itt_count == 0) && ((flags & INST_SET_FLAGS) != INST_NORMAL) {
            self.cmp(a, b, c)
        }
        self.cpu_set_register(flags, dest, val);
        Ok(())
    }
    fn cmp(&mut self, flags: InstructionFlags, a: Register, b: Shifted) -> Result<()> {
        let a = self.cpu_register(flags, a);
        let b = self.shifted(flags, b);
        self.cmp(a, b, 0);
        Ok(())
    }
    fn cmn(&mut self, flags: InstructionFlags, a: Register, b: Shifted) -> Result<()> {
        let a = self.cpu_register(flags, a);
        let b = self.shifted(flags, b);
        self.cmn(a, b, 0);
        Ok(())
    }

    // Bitwise
    fn and(&mut self, flags: InstructionFlags, dest: Register, src: ImmOrReg<Word>, operand: Shifted) -> Result<()> {
        let val = self.imm_or_reg(flags, src) & self.shifted(flags, operand);
        self.cpu_set_register(flags, dest, val);
        Ok(())
    }
    fn orr(&mut self, flags: InstructionFlags, dest: Register, src: ImmOrReg<Word>, operand: Shifted) -> Result<()> {
        let val = self.imm_or_reg(flags, src) | self.shifted(flags, operand);
        self.cpu_set_register(flags, dest, val);
        Ok(())
    }
    fn eor(&mut self, flags: InstructionFlags, dest: Register, src: ImmOrReg<Word>, operand: Shifted) -> Result<()> {
        let val = self.imm_or_reg(flags, src) ^ self.shifted(flags, operand);
        self.cpu_set_register(flags, dest, val);
        Ok(())
    }
    
    fn str(&mut self, flags: InstructionFlags, src: Register, dest: ImmOrReg<Word>, off: Shifted) -> Result<()> {
        let base = self.imm_or_reg(flags, dest);
        let addr = base + self.shifted(flags, off);
        let value = self.cpu_register(flags, src);
        
        if flags.get(INST_BYTE) {
            self.memory.write_u8(addr as u64, value as u8)
        } else if flags.get(INST_HALF) {
            self.memory.write_u16(addr as u64, value as u16)
        } else {
            self.memory.write_u32(addr as u64, value as u32)
        }
    }
    
    fn ldr(&mut self, flags: InstructionFlags, dest: Option<Register>, src: ImmOrReg<Word>, off: Shifted) -> Result<()> {        
        let base = self.imm_or_reg(flags, src);
        let addr = base + self.shifted(flags, off);
        let value;
        
        if flags.get(INST_BYTE) {
            value = try!(self.memory.read_u8(addr as u64)) as i32;
        } else if flags.get(INST_HALF) {
            value = try!(self.memory.read_u16(addr as u64)) as i32;
        } else {
            value = try!(self.memory.read_u32(addr as u64)) as i32;
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
            let i = 15-i;
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

            if let Ok(value) = self.memory.read_u32(addr as u64) {
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
            self.memory.write_u32(addr as u64, value as u32).ok();
            
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

    fn bkpt(&mut self, _code: i8) -> Result<()> {
        self.paused = true;
        self.send_gdb_command(&gdb::Command::new("S05"));
        Ok(())
    }
}
