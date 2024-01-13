//! <https://adventofcode.com/2020/day/8>
use crate::{
    framework::{aoc_at, AdventOfCode, ParseError},
    regex,
};

#[derive(Clone, Debug, PartialEq)]
enum Instruction {
    Acc(isize),
    Jmp(isize),
    Nop(isize),
}

/* impl ProblemObject for Instruction {
    fn parse(line: &str) -> Option<Instruction> {
        let re = regex!(r"^(acc|jmp|nop) ([+-])(\d+)$");
        if let Some(m) = re.captures(line) {
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
} */

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

#[derive(Debug, Default, PartialEq)]
pub struct Puzzle {
    code: Vec<(Instruction, bool)>,
}

#[aoc_at(2020, 8)]
impl AdventOfCode for Puzzle {
    type Output1 = isize;
    type Output2 = isize;
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        let re = regex!(r"^(acc|jmp|nop) ([+-])(\d+)$");
        if let Some(m) = re.captures(block) {
            let mnemonic = &m[1];
            let val = match (&m[2], &m[3]) {
                ("+", n) => n.parse::<isize>().ok(),
                ("-", n) => n.parse::<isize>().map(|n| -n).ok(),
                _ => None,
            };
            if let Some(n) = val {
                if let Some(inst) = Instruction::from(mnemonic, n) {
                    self.code.push((inst, false));
                    return Ok(());
                }
            } else {
                panic!("mnemonic.{}, sign.{}, val.{}", mnemonic, &m[2], &m[3]);
            }
        }
        Err(ParseError)
    }
    fn part1(&mut self) -> isize {
        if let Some(result) = CPU::run1(&mut self.code) {
            return result.accumulator;
        }
        0
    }
    fn part2(&mut self) -> isize {
        for i in 0..self.code.len() {
            if let Some(mut variant) = flip(&self.code, i) {
                if let Some(result) = CPU::run2(&mut variant) {
                    return result.accumulator;
                }
            }
        }
        0
    }
}

const ABORT: usize = 10_000_000_000_000;

#[allow(clippy::upper_case_acronyms)]
#[derive(Debug, PartialEq)]
struct CPU {
    accumulator: isize,
    ip: usize,
}

impl CPU {
    fn default() -> Self {
        CPU {
            accumulator: 0,
            ip: 0,
        }
    }
    fn run1(codes: &mut [(Instruction, bool)]) -> Option<CPU> {
        let mut cpu = CPU::default();
        loop {
            if cpu.stopped(codes) {
                return Some(cpu);
            }
            if cpu.should_be_stopped(codes) {
                return Some(cpu);
            }
            cpu.execute(codes);
            if cpu.ip == ABORT {
                return None;
            }
        }
    }
    fn run2(codes: &mut [(Instruction, bool)]) -> Option<CPU> {
        let mut cpu = CPU::default();
        loop {
            if cpu.stopped(codes) {
                return Some(cpu);
            }
            if cpu.should_be_stopped(codes) {
                return None;
            }
            cpu.execute(codes);
            if cpu.ip == ABORT {
                return None;
            }
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
            Instruction::Nop(_) => (),
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
        let first = codes[self.ip].1;
        codes[self.ip].1 = true;
        first
    }
}

fn flip(codes: &[(Instruction, bool)], at: usize) -> Option<Vec<(Instruction, bool)>> {
    let mut newcodes: Vec<(Instruction, bool)> = Vec::new();
    for (n, inst) in codes.iter().enumerate() {
        if n == at {
            if let Some(flipped) = inst.0.flip() {
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

#[cfg(feature = "y2020")]
#[cfg(test)]
mod test {
    use {
        super::*,
        crate::framework::{Answer, Description},
    };

    #[test]
    fn test_part1() {
        assert_eq!(
            Puzzle::solve(Description::FileTag("test".to_string()), 1),
            Answer::Part1(5)
        );
    }
    #[test]
    fn test_part2() {
        assert_eq!(
            Puzzle::solve(Description::FileTag("test".to_string()), 2),
            Answer::Part2(8)
        );
    }
}
