//! <https://adventofcode.com/2018/day/16>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]

use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::neighbors,
        line_parser, regex,
    },
    std::collections::HashMap,
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Vec<usize>>,
    rules: Vec<(Vec<usize>, Vec<usize>, Vec<usize>)>,
    input_mode: usize,
    input_buffer: Vec<Vec<usize>>,
}

#[aoc(2018, 16)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn header(&mut self, input: String) -> Result<String, ParseError> {
        self.input_mode = 0;
        let mut segment = input.split("\n\n\n\n");
        let rules = segment.next().ok_or(ParseError)?;
        for l in rules.split('\n') {
            self.parse_rule(l)?;
        }
        let data = segment.next().ok_or(ParseError)?;
        Ok(data.to_string())
    }
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.line
            .push(line_parser::to_usizes_spliting_with(block, &[' ', ','])?);
        Ok(())
    }
    fn after_insert(&mut self) {
        dbg!(&self.rules.len());
        dbg!(&self.line.len());
    }
    fn part1(&mut self) -> Self::Output1 {
        0
    }
    fn part2(&mut self) -> Self::Output2 {
        0
    }
}

impl Puzzle {
    fn parse_rule(&mut self, block: &str) -> Result<(), ParseError> {
        match self.input_mode {
            0 => {
                let parser = regex!(r"^Before: \[([0-9, ]+)\]$");
                let segment = parser.captures(block).ok_or(ParseError)?;
                assert!(self.input_buffer.is_empty());
                self.input_buffer.push(line_parser::to_usizes_spliting_with(
                    &segment[1],
                    &[' ', ','],
                )?);
                self.input_mode = 1;
            }
            1 => {
                self.input_buffer
                    .push(line_parser::to_usizes_spliting_with(block, &[' ', ','])?);
                self.input_mode = 2;
            }
            2 => {
                let parser = regex!(r"^After:  \[([0-9, ]+)\]$");
                let segment = parser.captures(block).ok_or(ParseError)?;
                let t2 = line_parser::to_usizes_spliting_with(&segment[1], &[' ', ','])?;
                let t1 = self.input_buffer.pop().unwrap();
                let t0 = self.input_buffer.pop().unwrap();
                self.rules.push((t0, t1, t2));
                self.input_mode = 3;
            }
            3 => {
                assert!(block.is_empty());
                self.input_mode = 0;
            }
            _ => unreachable!(),
        }
        Ok(())
    }
}
