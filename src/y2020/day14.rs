//! <https://adventofcode.com/2020/day/14>
use crate::framework::{aoc, AdventOfCode, ParseError};
use {lazy_static::lazy_static, regex::Regex, std::collections::HashMap};

#[derive(Clone, Debug, PartialEq)]
enum OP {
    Mask(usize, usize, Vec<usize>),
    Set(usize, usize),
}

impl OP {
    fn apply1_to(&self, v: usize) -> usize {
        if let OP::Mask(zs, os, _) = self {
            (v | os) & !zs
        } else {
            v
        }
    }
    fn apply2_to(&self, v: usize) -> Vec<usize> {
        if let OP::Mask(_, os, ms) = self {
            let base = v | os;
            let mut vec = Vec::new();
            for mut i in 0..2_i32.pow(ms.len() as u32) as usize {
                let mut addr = base;
                for loc in ms.iter() {
                    addr &= !(1 << loc);
                    addr |= (i % 2) << loc;
                    i /= 2;
                }
                vec.push(addr);
            }
            vec
        } else {
            vec![v]
        }
    }
}

#[derive(Debug, PartialEq)]
pub struct Puzzle {
    mask: OP,
    code: Vec<OP>,
}

impl Default for Puzzle {
    fn default() -> Self {
        Puzzle {
            mask: OP::Mask(0, 0, vec![]),
            code: Vec::new(),
        }
    }
}

#[aoc(2020, 14)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        lazy_static! {
            static ref MASK: Regex = Regex::new(r"^mask = ((X|0|1)+)").expect("wrong");
            static ref SET: Regex = Regex::new(r"^mem\[(\d+)\] = (\d+)").expect("wrong");
        }
        if let Some(m) = MASK.captures(block) {
            let zeros = m[1]
                .chars()
                .fold(0, |sum, letter| sum * 2 + if letter == '0' { 1 } else { 0 });
            let ones = m[1]
                .chars()
                .fold(0, |sum, letter| sum * 2 + if letter == '1' { 1 } else { 0 });
            let wilds = m[1]
                .chars()
                .enumerate()
                .fold(Vec::new(), |mut v, (i, letter)| {
                    if letter == 'X' {
                        v.push(35 - i);
                    }
                    v
                });
            self.code.push(OP::Mask(zeros, ones, wilds));
            return Ok(());
        }
        if let Some(m) = SET.captures(block) {
            let address = m[1].parse::<usize>().unwrap();
            let val = m[2].parse::<usize>().unwrap();
            self.code.push(OP::Set(address, val));
            return Ok(());
        }
        Err(ParseError)
    }
    fn part1(&mut self) -> usize {
        let mut mem: HashMap<usize, usize> = HashMap::new();
        for op in self.code.iter() {
            match op {
                OP::Mask(_, _, _) => {
                    self.mask = op.clone();
                }
                OP::Set(a, v) => {
                    *mem.entry(*a).or_insert(0) = self.mask.apply1_to(*v);
                }
            }
        }
        mem.values().sum::<usize>()
    }
    fn part2(&mut self) -> usize {
        let mut mem: HashMap<usize, usize> = HashMap::new();
        for op in self.code.iter() {
            match op {
                OP::Mask(_, _, _) => {
                    self.mask = op.clone();
                }
                OP::Set(a, v) => {
                    for addr in self.mask.apply2_to(*a).iter() {
                        *mem.entry(*addr).or_insert(0) = *v;
                    }
                }
            }
        }
        mem.values().sum::<usize>()
    }
}

#[cfg(test)]
#[cfg(feature = "y2020")]
mod test {
    use {
        super::*,
        crate::framework::{Answer, Description},
    };

    #[test]
    fn test_part1() {
        assert_eq!(
            Puzzle::solve(Description::FileTag("test1".to_string()), 1),
            Answer::Part1(165)
        );
    }
    #[test]
    fn test_part2() {
        assert_eq!(
            Puzzle::solve(Description::FileTag("test2".to_string()), 2),
            Answer::Part2(208)
        );
    }
}
