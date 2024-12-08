//! <https://adventofcode.com/2022/day/4>
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        parser::parse_usize,
    },
    winnow::{combinator::terminated, PResult, Parser},
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<(usize, usize, usize, usize)>,
}

fn parse_line(s: &mut &str) -> PResult<(usize, usize, usize, usize)> {
    (
        terminated(parse_usize, "-"),
        terminated(parse_usize, ","),
        terminated(parse_usize, "-"),
        parse_usize,
    )
        .parse_next(s)
}

#[aoc(2022, 4)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        /* let parser = regex!(r"^(\d+)-(\d+),(\d+)-(\d+)$");
        let segment = parser.captures(block).ok_or(ParseError)?;
        self.line.push((
            segment[1].parse::<_>()?,
            segment[2].parse::<_>()?,
            segment[3].parse::<_>()?,
            segment[4].parse::<_>()?,
        )); */
        let s = block.to_string();
        let p = &mut s.as_str();
        self.line.push(parse_line(p)?);
        Ok(())
    }
    fn end_of_data(&mut self) {
        // dbg!(&self.line);
    }
    fn part1(&mut self) -> Self::Output1 {
        self.line
            .iter()
            .filter(|(a, b, x, y)| (a <= x && y <= b) || (x <= a && b <= y))
            .count()
    }
    fn part2(&mut self) -> Self::Output2 {
        self.line
            .iter()
            .filter(|(a, b, x, y)| (x <= b) && (a <= y))
            .count()
    }
}
