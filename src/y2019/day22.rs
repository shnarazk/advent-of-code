//! <https://adventofcode.com/2019/day/22>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::neighbors,
        line_parser, regex,
    },
    std::collections::HashSet,
};

#[derive(Debug, Eq, Hash, PartialEq)]
enum Shuffle<const N: usize> {
    Stack,
    Cut(isize),
    Increment(usize),
}
const PART1_SIZE: usize = 10007;
const PART2_SIZE: usize = 119315717514047;

impl<const N: usize> Shuffle<N> {
    fn part1(&self) -> Shuffle<PART1_SIZE> {
        match self {
            Self::Stack => Shuffle::<PART1_SIZE>::Stack,
            Self::Cut(c) => Shuffle::<PART1_SIZE>::Cut(*c),
            Self::Increment(i) => Shuffle::<PART1_SIZE>::Increment(*i),
        }
    }
    fn part2(&self) -> Shuffle<PART2_SIZE> {
        match self {
            Self::Stack => Shuffle::<PART2_SIZE>::Stack,
            Self::Cut(c) => Shuffle::<PART2_SIZE>::Cut(*c),
            Self::Increment(i) => Shuffle::<PART2_SIZE>::Increment(*i),
        }
    }
    fn shuffle(&self, n: usize) -> usize {
        match self {
            Shuffle::Stack => N - 1 - n,
            Shuffle::Cut(c) => (((N + n) as isize - *c) as usize) % N,
            Shuffle::Increment(i) => (n * i) % N,
        }
    }
}

#[derive(Debug, Default, Eq, Hash, PartialEq)]
pub struct Puzzle {
    line: Vec<Shuffle<0>>,
}

#[aoc(2019, 22)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        let stack = regex!(r"^deal into new stack$");
        let cut = regex!(r"^cut (-?\d+)$");
        let increment = regex!(r"^deal with increment (\d+)$");
        if let Some(segment) = stack.captures(block) {
            self.line.push(Shuffle::Stack);
        } else if let Some(segment) = cut.captures(block) {
            let val: isize = segment[1].parse::<isize>()?;
            self.line.push(Shuffle::Cut(val));
        } else if let Some(segment) = increment.captures(block) {
            let val: usize = segment[1].parse::<usize>()?;
            self.line.push(Shuffle::Increment(val));
        }
        Ok(())
    }
    fn after_insert(&mut self) {
        // dbg!(&self.line.len());
    }
    fn part1(&mut self) -> Self::Output1 {
        self.line
            .iter()
            .fold(2019_usize, |i, s| s.part1().shuffle(i))
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut index: usize = 2020;
        let suit = self.line.iter().map(|t| t.part2()).collect::<Vec<_>>();
        for i in 0..101_741_582_076_661_usize {
            index = suit.iter().fold(index, |i, t| t.shuffle(i));
        }
        index
    }
}
