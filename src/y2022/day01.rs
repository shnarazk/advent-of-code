//! <https://adventofcode.com/2022/day/1>
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        parser::parse_usize,
    },
    winnow::{ascii::newline, combinator::separated, PResult, Parser},
};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Vec<usize>>,
}

fn parse_block(s: &mut &str) -> PResult<Vec<usize>> {
    separated(1.., parse_usize, newline).parse_next(s)
}
fn parse(s: &mut &str) -> PResult<Vec<Vec<usize>>> {
    separated(1.., parse_block, (newline, newline)).parse_next(s)
}

#[aoc(2022, 1)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n\n";
    fn parse(&mut self, input: String) -> Result<String, ParseError> {
        let s = &mut input.as_str();
        self.line = parse(s)?;
        Ok("".to_string())
    }
    fn end_of_data(&mut self) {
        dbg!(&self.line);
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
