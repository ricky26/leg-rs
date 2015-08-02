use super::{
    Error, Result, Register, ExecutionContext, ImmOrReg, InstructionFlags, Condition,
    INST_NORMAL, INST_SET_FLAGS,
};

pub trait IntTruncate {
    fn int_truncate(src: i32) -> Self;
}

impl IntTruncate for i32 {
    fn int_truncate(src: i32) -> i32 { src }
}

impl IntTruncate for i16 {
    fn int_truncate(src: i32) -> i16 { src as i16 }
}

impl IntTruncate for i8 {
    fn int_truncate(src: i32) -> i8 { src as i8 }
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
}

pub struct SimpleEmulator<M: Memory> {
    pub memory: M,
    
    registers: [i32;16],
    apsr: u32,
    itt_mask: u8,
    itt_count: i8,
}

impl<M: Memory> SimpleEmulator<M> {
    pub fn new(memory: M) -> SimpleEmulator<M> {
        SimpleEmulator {
            registers: [0i32;16],
            apsr: 0u32,
            memory: memory,
            itt_mask: 0u8,
            itt_count: 0,
        }
    }

    pub fn register(&self, reg: Register) -> i32 {
        self.registers[reg.index() as usize]
    }

    pub fn set_register(&mut self, reg: Register, value: i32) {
        self.registers[reg.index() as usize] = value
    }

    pub fn imm_or_reg<T: IntTruncate>(&self, imm_or_reg: ImmOrReg<T>) -> T {
        match imm_or_reg {
            ImmOrReg::Reg(x) => T::int_truncate(self.register(x)),
            ImmOrReg::Imm(x) => x,
        }
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

    pub fn cmp(&mut self, a: i32, b: i32, c: i32) {
        let ua = a as u32;
        let ub = b as u32;
        let uc = c as u32;
        
        let mut apsr = (ua - ub - uc) & 0x80000000;
        
        if ua == ub {
            apsr |= 1u32 << 30
        }
        if ua > ub {
            apsr |= 1u32 << 29
        }
        if ((a < 0) && (b > (2147483647-a+1)))
            || ((a > 0) && (-b > (a-2147483647))) {
                apsr |= 1u32 << 28
            }

        self.set_apsr(apsr)
    }

    pub fn cmn(&mut self, a: i32, b: i32, c: i32) {
        let ua = a as u32;
        let ub = b as u32;
        let uc = c as u32;
        
        let mut apsr = (ua + ub + uc) & 0x80000000;
        
        if (ua + ub) == 0 {
            apsr |= 1u32 << 30
        }
        if (4294967295u32 - ua) > ub {
            apsr |= 1u32 << 29
        }
        if ((a < 0) && (b < -(2147483647-a+1)))
            || ((a > 0) && (b > (a-2147483647))) {
                apsr |= 1u32 << 28
            }

        self.set_apsr(apsr)
    }

    pub fn execute_buffer<'a>(&mut self, buffer: &'a [u8]) -> (&'a [u8], Result<()>) {
        // TODO: Check ARM/THUMB mode.
        super::thumb::execute(self, buffer)
    }

    pub fn execute_one(&mut self) -> Result<()> {
        let mut buf = [0u8; 4];
        let mut pc = self.register(Register::PC);

        try!(self.memory.read(pc as u64, &mut buf[..2]));
        pc += 2;

        let (_, mut err) = self.execute_buffer(&mut buf[..2]);
        if let Err(Error::NotEnoughInput(_)) = err {
            try!(self.memory.read(pc as u64, &mut buf[2..4]));
            pc += 2;
            
            match self.execute_buffer(&mut buf[..4]) {
                (_, e) => { err = e; },
            }
        }

        if let Ok(()) = err {
            self.set_register(Register::PC, pc);
        }
        err
    }

    pub fn execute(&mut self) -> Result<()> {
        loop {
            try!(self.execute_one());
        }

        Ok(())
    }
}


impl<'a, M: Memory> ExecutionContext for SimpleEmulator<M> {
    fn undefined(&mut self) {
        panic!("undefined")
    }
    fn unpredictable(&mut self) {
        panic!("unpredictable")
    }
    
    // Move
    fn mov(&mut self, flags: InstructionFlags, dest: Register, src: ImmOrReg<i32>) {
        let val = self.imm_or_reg(src);
        if (self.itt_count == 0) && ((flags & INST_SET_FLAGS) != INST_NORMAL) {
            self.cmn(val, 0, 0)
        }
        self.set_register(dest, val)
    }
    
    fn adr(&mut self, dest: Register, offset: ImmOrReg<i32>) {
        let val = self.register(Register::PC) + self.imm_or_reg(offset);
        self.set_register(dest, val)
    }

    // Add/subtract
    fn add(&mut self, flags: InstructionFlags, dest: Register, src: ImmOrReg<i32>, add: ImmOrReg<i32>) {
        println!("add {:?}, {:?}, {:?}", dest, src, add);
        let a = self.imm_or_reg(src);
        let b = self.imm_or_reg(add);
        let val = a + b;
        if (self.itt_count == 0) && ((flags & INST_SET_FLAGS) != INST_NORMAL) {
            self.cmn(a, b, 0)
        }
        self.set_register(dest, val)
    }
    fn sub(&mut self, flags: InstructionFlags, dest: Register, src: ImmOrReg<i32>, sub: ImmOrReg<i32>) {
        let a = self.imm_or_reg(src);
        let b = self.imm_or_reg(sub);
        let val = a - b;
        if (self.itt_count == 0) && ((flags & INST_SET_FLAGS) != INST_NORMAL) {
            self.cmp(a, b, 0)
        }
        self.set_register(dest, val)
    }
    fn rsb(&mut self, flags: InstructionFlags, dest: Register, src: ImmOrReg<i32>, sub: ImmOrReg<i32>) {
        let a = self.imm_or_reg(src);
        let b = self.imm_or_reg(sub);
        let val = b - a;
        if (self.itt_count == 0) && ((flags & INST_SET_FLAGS) != INST_NORMAL) {
            self.cmp(b, a, 0)
        }
        self.set_register(dest, val)
    }
    fn adc(&mut self, flags: InstructionFlags, dest: Register, src: ImmOrReg<i32>, add: ImmOrReg<i32>) {
        let a = self.imm_or_reg(src);
        let b = self.imm_or_reg(add);
        let c = self.carry() as i32;
        let val = a + b + c;
        if (self.itt_count == 0) && ((flags & INST_SET_FLAGS) != INST_NORMAL) {
            self.cmn(a, b, c)
        }
        self.set_register(dest, val)
    }
    fn sbc(&mut self, flags: InstructionFlags, dest: Register, src: ImmOrReg<i32>, sub: ImmOrReg<i32>) {
        let a = self.imm_or_reg(src);
        let b = self.imm_or_reg(sub);
        let c = self.carry() as i32;
        let val = a - b - c;
        if (self.itt_count == 0) && ((flags & INST_SET_FLAGS) != INST_NORMAL) {
            self.cmp(a, b, c)
        }
        self.set_register(dest, val)
    }
    fn cmp(&mut self, _flags: InstructionFlags, a: Register, b: ImmOrReg<i32>) {
        let a = self.register(a);
        let b = self.imm_or_reg(b);
        self.cmp(a, b, 0)
    }
    fn cmn(&mut self, _flags: InstructionFlags, a: Register, b: ImmOrReg<i32>) {
        let a = self.register(a);
        let b = self.imm_or_reg(b);
        self.cmn(a, b, 0)
    }

    // Bitwise
    fn and(&mut self, _flags: InstructionFlags, dest: Register, src: ImmOrReg<i32>, operand: ImmOrReg<i32>) {
        let val = self.imm_or_reg(src) & self.imm_or_reg(operand);
        self.set_register(dest, val)
    }
    fn orr(&mut self, _flags: InstructionFlags, dest: Register, src: ImmOrReg<i32>, operand: ImmOrReg<i32>) {
        let val =self.imm_or_reg(src) | self.imm_or_reg(operand);
        self.set_register(dest, val)
    }
    fn eor(&mut self, _flags: InstructionFlags, dest: Register, src: ImmOrReg<i32>, operand: ImmOrReg<i32>) {
        let val = self.imm_or_reg(src) ^ self.imm_or_reg(operand);
        self.set_register(dest, val)
    }
    fn lsl(&mut self, _flags: InstructionFlags, dest: Register, src: ImmOrReg<i32>, operand: ImmOrReg<i8>) {
        let val = self.imm_or_reg(src) << self.imm_or_reg(operand);
        self.set_register(dest, val)
    }
    fn lsr(&mut self, _flags: InstructionFlags, dest: Register, src: ImmOrReg<i32>, operand: ImmOrReg<i8>) {
        let val = ((self.imm_or_reg(src) as u32) >> (self.imm_or_reg(operand) as u32)) as i32;
        self.set_register(dest, val)
    }
    fn asr(&mut self, _flags: InstructionFlags, dest: Register, src: ImmOrReg<i32>, operand: ImmOrReg<i8>) {
        let val = self.imm_or_reg(src) >> self.imm_or_reg(operand);
        self.set_register(dest, val)
    }
    fn ror(&mut self, _flags: InstructionFlags, dest: Register, src: ImmOrReg<i32>, operand: ImmOrReg<i8>) {
        let src = self.imm_or_reg(src) as u32;
        let shift = self.imm_or_reg(operand);
        let val = (src >> shift) | (src << (32-shift));
        self.set_register(dest, val as i32)
    }
    
    fn ldm(&mut self, _flags: InstructionFlags, _dest: Register, _registers: u16, _inc: bool) { }
    fn stm(&mut self, _flags: InstructionFlags, _dest: Register, _registers: u16, _inc: bool) { }
}
