//! <https://adventofcode.com/2022/day/10>
use crate::{
    framework::{aoc_at, AdventOfCode, ParseError},
    regex,
};

#[derive(Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Code {
    Noop,
    Addx(isize),
}
#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Code>,
    pc: usize,
    register: isize,
    cycle: usize,
    auto_sum: isize,
    state: Option<isize>,
}

#[aoc_at(2022, 10)]
impl AdventOfCode for Puzzle {
    type Output1 = isize;
    type Output2 = isize;
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        let addx_parser = regex!(r"^addx (-?\d+)$");
        let noop_parser = regex!(r"^noop$");
        if let Some(segment) = addx_parser.captures(block) {
            self.line.push(Code::Addx(segment[1].parse::<isize>()?));
        } else if noop_parser.captures(block).is_some() {
            self.line.push(Code::Noop);
        }
        Ok(())
    }
    fn after_insert(&mut self) {
        self.register = 1;
        dbg!(&self.line.len());
    }
    fn part1(&mut self) -> Self::Output1 {
        for _ in 0..self.line.len() {
            self.execute();
        }
        self.auto_sum
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut crt: [char; 240] = ['.'; 240];
        for cycle in 0_isize..240 {
            if (cycle % 40).abs_diff(self.register) <= 1 {
                crt[cycle as usize] = '#';
            }
            self.cycle_wise_execute();
        }
        for (i, c) in crt.iter().enumerate() {
            print!("{}", c);
            if i % 40 == 39 {
                println!();
            }
        }
        self.auto_sum
    }
}

impl Puzzle {
    fn signal_strength(&self) -> isize {
        self.cycle as isize * self.register
    }
    fn update_cycle(&mut self, n: usize) {
        for _ in 0..n {
            self.cycle += 1;
            if 20 <= self.cycle && (self.cycle - 20) % 40 == 0 {
                self.auto_sum += self.signal_strength();
            }
        }
    }
    fn execute(&mut self) {
        let Some(inst) = &self.line.get(self.pc) else { return; };
        match inst {
            Code::Noop => {
                self.update_cycle(1);
            }
            Code::Addx(n) => {
                let k = *n;
                self.update_cycle(1);
                self.update_cycle(1);
                self.register += k;
            }
        }
        self.pc += 1;
    }
    fn cycle_wise_execute(&mut self) {
        if let Some(adding) = self.state {
            self.update_cycle(1);
            self.register += adding;
            self.pc += 1;
            self.state = None;
        } else {
            let Some(inst) = &self.line.get(self.pc) else { return; };
            match inst {
                Code::Noop => {
                    self.update_cycle(1);
                    self.pc += 1;
                }
                Code::Addx(n) => {
                    let k = *n;
                    self.update_cycle(1);
                    self.state = Some(k);
                }
            }
        }
    }
}
