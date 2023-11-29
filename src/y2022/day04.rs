//! <https://adventofcode.com/2022/day/4>
use crate::{
    framework::{aoc, AdventOfCode, ParseError},
    regex,
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<(usize, usize, usize, usize)>,
}

#[aoc(2022, 4)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        let parser = regex!(r"^(\d+)-(\d+),(\d+)-(\d+)$");
        let segment = parser.captures(block).ok_or(ParseError)?;
        self.line.push((
            segment[1].parse::<_>()?,
            segment[2].parse::<_>()?,
            segment[3].parse::<_>()?,
            segment[4].parse::<_>()?,
        ));
        Ok(())
    }
    fn wrap_up(&mut self) {
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
