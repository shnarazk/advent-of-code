//! <https://adventofcode.com/2019/day/9>

use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        line_parser,
    },
    std::collections::{HashMap, VecDeque},
};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<isize>,
    pc: usize,
}

#[aoc(2019, 9)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.line = line_parser::to_isizes(block, ',')?;
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut inputs = VecDeque::new();
        inputs.push_back(1);
        self.execute(&mut inputs)[0] as usize
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut inputs = VecDeque::new();
        inputs.push_back(2);
        self.execute(&mut inputs)[0] as usize
    }
}

impl Puzzle {
    fn execute(&mut self, inputs: &mut VecDeque<isize>) -> Vec<isize> {
        let mut memory: HashMap<usize, isize> = HashMap::new();
        for (i, v) in self.line.iter().enumerate() {
            memory.insert(i, *v);
        }
        let mut output: Vec<isize> = Vec::new();
        let mut pc: usize = 0;
        let mut r_base: usize = 0;
        loop {
            let op = memory[&pc] % 100;
            let immediate: Vec<u8> = {
                let mut v = Vec::new();
                let mut val = memory[&pc] / 100;
                while 0 < val {
                    v.push((val % 10) as u8);
                    val /= 10;
                }
                v
            };
            macro_rules! deref {
                ($offset: expr) => {{
                    match immediate.get($offset - 1) {
                        Some(0) | None => memory[&(pc + $offset)] as usize,
                        Some(1) => (pc + $offset) as usize,
                        Some(2) => (r_base as isize + memory[&(pc + $offset)]) as usize,
                        _ => unreachable!(),
                    }
                }};
                ($offset: expr, true) => {{
                    match immediate.get($offset - 1) {
                        Some(0) | None => memory[&(memory[&(pc + $offset)] as usize)],
                        Some(1) => memory[&(pc + $offset)],
                        Some(2) => memory[&((r_base as isize + memory[&(pc + $offset)]) as usize)],
                        _ => unreachable!(),
                    }
                }};
            }
            match op {
                1 => {
                    let dst = deref!(3);
                    memory.insert(dst, deref!(1, true) + deref!(2, true));
                    pc += 4;
                }
                2 => {
                    let dst = deref!(3);
                    memory.insert(dst, deref!(1, true) * deref!(2, true));
                    pc += 4;
                }
                3 => {
                    let dst = deref!(1);
                    // println!("input at {pc}");
                    memory.insert(dst, inputs.pop_front().expect("not enough input"));
                    pc += 2;
                }
                4 => {
                    let op1 = deref!(1, true);
                    output.push(op1);
                    pc += 2;
                }
                5 => {
                    let op1 = deref!(1, true);
                    let op2 = deref!(2, true);
                    if 0 != op1 {
                        pc = op2 as usize;
                    } else {
                        pc += 3;
                    }
                }
                6 => {
                    let op1 = deref!(1, true);
                    let op2 = deref!(2, true);
                    if 0 == op1 {
                        pc = op2 as usize;
                    } else {
                        pc += 3;
                    }
                }
                7 => {
                    let op1 = deref!(1, true);
                    let op2 = deref!(2, true);
                    let dst = deref!(3);
                    memory.insert(dst, (op1 < op2) as usize as isize);
                    pc += 4;
                }
                8 => {
                    let op1 = deref!(1, true);
                    let op2 = deref!(2, true);
                    let dst = deref!(3);
                    memory.insert(dst, (op1 == op2) as usize as isize);
                    pc += 4;
                }
                9 => {
                    let op1 = deref!(1, true);
                    r_base = (r_base as isize + op1) as usize;
                    pc += 2;
                }
                99 => {
                    break;
                }
                _ => panic!("op: {op} at {pc}"),
            }
        }
        assert!(1 == output.len());
        output
    }
}
