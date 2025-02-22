//! <https://adventofcode.com/2016/day/09>

use crate::framework::{AdventOfCode, ParseError, aoc};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: String,
}

mod parser {
    use {
        crate::parser::parse_usize,
        winnow::{ModalResult, Parser, ascii::alpha0, combinator::seq},
    };

    pub fn parse_line(s: &mut &str) -> ModalResult<(String, usize, usize)> {
        seq!(alpha0, _: "(", parse_usize, _: "x", parse_usize, _: ")")
            .map(|(s, a, b)| (s.to_string(), a, b))
            .parse_next(s)
    }
}

#[aoc(2016, 9)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, input: &str) -> Result<(), ParseError> {
        self.line = input.chars().filter(|c| *c != '\n').collect();
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut buffer: &str = self.line.trim();
        let mut length = 0;
        while let Ok((segment, len, rep)) = parser::parse_line(&mut buffer) {
            length += segment.len() + len * rep;
            buffer = &buffer[len..];
        }
        length
    }
    fn part2(&mut self) -> Self::Output2 {
        span_len(self.line.trim())
    }
}

fn span_len(buffer: &str) -> usize {
    let mut b = buffer;
    let mut p = b;
    let mut length = 0;
    loop {
        if let Ok((segment, len, rep)) = parser::parse_line(&mut b) {
            length += segment.len() + rep * span_len(&b[0..len]);
            b = &b[len..];
            p = b;
        } else {
            return length + p.len();
        }
    }
}
