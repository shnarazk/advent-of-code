//! <https://adventofcode.com/2016/day/09>
use crate::{
    framework::{aoc, AdventOfCode, ParseError},
    regex,
};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: String,
}

#[aoc(2016, 9)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.line = block.to_string();
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut buffer: &str = self.line.trim();
        let mut length = 0;
        let parser = regex!(r"([^(]*)\((\d+)x(\d+)\)");
        while let Some(segment) = parser.captures(buffer) {
            let len = segment[2].parse::<usize>().unwrap();
            let rep = segment[3].parse::<usize>().unwrap();
            length += segment[1].len() + len * rep;
            buffer = &buffer[segment[0].len() + len..];
        }
        length += buffer.len();
        length
    }
    fn part2(&mut self) -> Self::Output2 {
        span_len(self.line.trim())
    }
}

fn span_len(mut buffer: &str) -> usize {
    let mut length = 0;
    let parser = regex!(r"([^(]*)\((\d+)x(\d+)\)");
    while let Some(segment) = parser.captures(buffer) {
        let len = segment[2].parse::<usize>().unwrap();
        let rep = segment[3].parse::<usize>().unwrap();
        length +=
            segment[1].len() + rep * span_len(&buffer[segment[0].len()..segment[0].len() + len]);
        buffer = &buffer[segment[0].len() + len..];
    }
    length += buffer.len();
    length
}
