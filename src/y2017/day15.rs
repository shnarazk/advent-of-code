//! <https://adventofcode.com/2017/day/15>
use crate::{
    framework::{aoc, AdventOfCode, ParseError},
    regex,
};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    factor: (usize, usize),
    line: Vec<usize>,
}

#[aoc(2017, 15)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        // Generator B starts with 325
        let parser = regex!(r"^Generator (A|B) starts with (\d+)$");
        let segment = parser.captures(block).ok_or(ParseError)?;
        self.line.push(segment[2].parse::<usize>()?);
        Ok(())
    }
    fn end_of_data(&mut self) {
        self.factor = (16807, 48271);
    }
    fn part1(&mut self) -> Self::Output1 {
        let m = 2147483647;
        let mask: usize = 2_usize.pow(16) - 1;
        let mut values: (usize, usize) = (self.line[0], self.line[1]);
        let mut count = 0;
        for _ in 0..40_000_000 {
            values.0 = (values.0 * self.factor.0) % m;
            values.1 = (values.1 * self.factor.1) % m;
            if values.0 & mask == values.1 & mask {
                count += 1;
            }
        }
        count
    }
    fn part2(&mut self) -> Self::Output2 {
        let modulo = 2147483647;
        let mask: usize = 2_usize.pow(16) - 1;
        let mut g1: Generator = Generator {
            value: self.line[0],
            factor: self.factor.0,
            modulo,
            mask,
            check: 4,
        };
        let mut g2: Generator = Generator {
            value: self.line[1],
            factor: self.factor.1,
            modulo,
            mask,
            check: 8,
        };
        (0..5_000_000)
            .filter(|_| g1.next().unwrap() == g2.next().unwrap())
            .count()
    }
}

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Generator {
    value: usize,
    factor: usize,
    modulo: usize,
    mask: usize,
    check: usize,
}

impl Iterator for Generator {
    type Item = usize;
    fn next(&mut self) -> Option<Self::Item> {
        let mut n = self.value;
        loop {
            n = (n * self.factor) % self.modulo;
            if n % self.check == 0 {
                self.value = n;
                return Some(n & self.mask);
            }
        }
    }
}
