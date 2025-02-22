//! <https://adventofcode.com/2022/day/1>
use {
    crate::{
        framework::{AdventOfCode, ParseError, aoc},
        parser::parse_usize,
    },
    winnow::{ModalResult, Parser, ascii::newline, combinator::separated},
};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Vec<usize>>,
}

fn parse_block(s: &mut &str) -> ModalResult<Vec<usize>> {
    separated(1.., parse_usize, newline).parse_next(s)
}
fn parse(s: &mut &str) -> ModalResult<Vec<Vec<usize>>> {
    separated(1.., parse_block, (newline, newline)).parse_next(s)
}

#[aoc(2022, 1)]
impl AdventOfCode for Puzzle {
    fn prepare(&mut self, mut input: &str) -> Result<(), ParseError> {
        self.line = parse(&mut input)?;
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        self.line.iter().map(|v| v.iter().sum()).max().unwrap()
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut elves = self
            .line
            .iter()
            .map(|v| v.iter().sum())
            .collect::<Vec<usize>>();
        // dbg!(&elves);
        elves.sort();
        elves.iter().skip(elves.len() - 3).sum()
    }
}
