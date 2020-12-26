#![allow(dead_code)]
#![allow(unused_variables)]
use {
    lazy_static::lazy_static,
    regex::Regex,
    std::{
        io::{self, Read},
    },
};

#[derive(Clone, Debug, PartialEq)]
enum Instruction {
    Acc(isize),
    Jmp(isize),
    Nop(isize),
}

impl Instruction {
    fn from(mnemonic: &str, n: isize) -> Option<Self> {
        match mnemonic {
            "acc" => Some(Instruction::Acc(n)),
            "jmp" => Some(Instruction::Jmp(n)),
            "nop" => Some(Instruction::Nop(n)),
            _ => None,
        }
    }
    fn flip(&self) -> Option<Instruction> {
        match self {
            Instruction::Acc(_) => None,
            Instruction::Jmp(n) => Some(Instruction::Nop(*n)),
            Instruction::Nop(n) => Some(Instruction::Jmp(*n)),
        }
    }
}

#[derive(Debug, PartialEq)]
struct CPU {
    accumulator: isize,
    ip: usize,
}

impl Default for CPU {
    fn default() -> Self {
        CPU {
            accumulator: 0,
            ip: 0
        }
    }
}

const ABORT: usize = 10_000_000_000_000;

impl CPU {
    fn run(codes: &mut [(Instruction, bool)]) -> Option<CPU> {
        let mut cpu = CPU::default();
        cpu.ip = 0;
        loop {
            if cpu.stopped(codes) {
                return Some(cpu);
            }
            if cpu.should_be_stopped(codes) {
                return None;
            }
            cpu.execute(codes);
        }
   }
    fn decode(&mut self, inst: &Instruction) {
        match inst {
            Instruction::Acc(n) => {
                self.accumulator += n;
            }
            Instruction::Jmp(n) => {
                let new_ip = self.ip as isize + n - 1;
                if new_ip < 0 {
                    self.ip = ABORT;
                } else {
                    self.ip = new_ip as usize;
                }
            }
            Instruction::Nop(n) => (),
        }
    }
    fn execute(&mut self, codes: &[(Instruction, bool)]) {
        let code = &codes[self.ip].0;
        self.decode(code);
        if self.ip < ABORT {
            self.ip += 1;
        }
    }
    fn stopped(&mut self, codes: &mut [(Instruction, bool)]) -> bool {
        codes.len() == self.ip
    }
    fn should_be_stopped(&mut self, codes: &mut [(Instruction, bool)]) -> bool {
        if self.ip == ABORT {
            return true;
        }
        let first = codes[self.ip].1;
        codes[self.ip].1 = true;
        first
    }
}

pub fn day08() {
    let mut buffer = String::new();
    io::stdin()
        .read_to_string(&mut buffer)
        .expect("something wrong");

    let mut codes: Vec<(Instruction, bool)> = Vec::new();

    for line in buffer.split('\n') {
        if line.is_empty() {
            break;
        }
        if let Some(c) = parse(line) {
            codes.push((c, false));
        } else {
            panic!("wrong code");
        }
    }
    for i in 0..codes.len() {
        if let Some(mut variant) = flip(&codes, i) {
            if let Some(result) = CPU::run(&mut variant) {
                dbg!(result);
                return;
            }
        }
    }
}

fn parse(line: &str) -> Option<Instruction> {
    lazy_static! {
        static ref RE: Regex = Regex::new(r"^(acc|jmp|nop) ([+-])(\d+)$").expect("bad");
    }
    if let Some(m) = RE.captures(line) {
        let mnemonic = &m[1];
        let val = match (&m[2], &m[3]) {
            ("+", n) => n.parse::<isize>().ok(),
            ("-", n) => n.parse::<isize>().map(|n| -n).ok(),
            _ => None,
        };
        if let Some(n) = val {
            return Instruction::from(mnemonic, n);
        } else {
            panic!("mnemonic.{}, sign.{}, val.{}", mnemonic, &m[2], &m[3]);
        }
    }
    None
}

fn flip(codes: &[(Instruction, bool)], at: usize) -> Option<Vec<(Instruction, bool)>> {
    let mut newcodes: Vec<(Instruction, bool)> = Vec::new();
    for (n, inst) in codes.iter().enumerate() {
        if n == at {
            if let Some(flipped) = inst.0.flip() {
                dbg!((n, &flipped));
                newcodes.push((flipped, false));
            } else {
                return None;
            }
        } else {
            newcodes.push((inst.0.clone(), false));
        }
    }
    Some(newcodes)
}
