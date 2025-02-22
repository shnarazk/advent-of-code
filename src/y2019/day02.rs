//! <https://adventofcode.com/2019/day/2>
use {
    crate::{
        framework::{AdventOfCode, ParseError, aoc},
        parser,
    },
    std::collections::HashMap,
};

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Puzzle {
    line: Vec<isize>,
    memory: HashMap<usize, isize>,
}

#[aoc(2019, 2)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, input: &str) -> Result<(), ParseError> {
        self.line = parser::to_isizes(input, &[','])?;
        for (i, v) in self.line.iter().enumerate() {
            self.memory.insert(i, *v);
        }
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        self.memory.insert(1, 12);
        self.memory.insert(2, 2);
        self.start();
        self.memory[&0] as usize
    }
    fn part2(&mut self) -> Self::Output2 {
        for c1 in 0..100 {
            for c2 in 0..100 {
                let mut processor = self.clone();
                processor.memory.insert(1, c1);
                processor.memory.insert(2, c2);
                processor.start();
                if processor.memory[&0] as usize == 19690720 {
                    return (processor.memory[&1] * 100 + processor.memory[&2]) as usize;
                }
            }
        }
        0
    }
}
impl Puzzle {
    fn start(&mut self) {
        let mut pc: usize = 0;
        let r_base: usize = 0;
        loop {
            let op = self.memory[&pc] % 100;
            // println!("opcode {} at {}", op, pc);
            let immediate: Vec<u8> = {
                let mut v = Vec::new();
                let mut val = self.memory[&pc] / 100;
                while 0 < val {
                    v.push((val % 10) as u8);
                    val /= 10;
                }
                v
            };
            macro_rules! deref {
                ($offset: expr) => {{
                    match immediate.get($offset - 1) {
                        Some(0) | None => self.memory[&(pc + $offset)] as usize,
                        Some(1) => (pc + $offset) as usize,
                        Some(2) => (r_base as isize + self.memory[&(pc + $offset)]) as usize,
                        _ => unreachable!(),
                    }
                }};
                ($offset: expr, true) => {{
                    let addr: usize = match immediate.get($offset - 1) {
                        Some(0) | None => self.memory[&(pc + $offset)] as usize,
                        Some(1) => pc + $offset,
                        Some(2) => (r_base as isize + self.memory[&(pc + $offset)]) as usize,
                        _ => unreachable!(),
                    };
                    self.memory.get(&addr).map_or(0, |p| *p)
                }};
            }
            match op {
                1 => {
                    let op1 = deref!(1, true);
                    let op2 = deref!(2, true);
                    let dst = deref!(3);
                    self.memory.insert(dst, op1 + op2);
                    pc += 4;
                }
                2 => {
                    let op1 = deref!(1, true);
                    let op2 = deref!(2, true);
                    let dst = deref!(3);
                    self.memory.insert(dst, op1 * op2);
                    pc += 4;
                }
                99 => {
                    break;
                }
                _ => panic!("op: {op} at {pc}"),
            }
        }
    }
}
