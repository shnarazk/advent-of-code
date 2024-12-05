//! <https://adventofcode.com/2024/day/13>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::neighbors,
    },
    serde::Serialize,
    std::collections::HashMap,
    winnow::{
        ascii::{dec_uint, newline},
        combinator::{repeat_till, separated},
        token::literal,
        PResult, Parser,
    },
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
pub struct Puzzle {
    line: Vec<()>,
}

// impl Default for Puzzle {
//     fn default() -> Self {
//         Puzzle { }
//     }
// }

// fn parse(str: &muut &str) -> PResult<()> {}

#[aoc(2024, 13)]
impl AdventOfCode for Puzzle {
    // const DELIMITER: &'static str = "\n";
    // fn parse(&mut self, input: String) -> Result<String, ParseError> {
    //     let parser = regex!(r"^(.+)\n\n((.|\n)+)$");
    //     let segment = parser.captures(input).ok_or(ParseError)?;
    //     for num in segment[1].split(',') {
    //         let _value = num.parse::<usize>()?;
    //     }
    //     // Ok("".to_string())
    //     Ok(segment[2].to_string())
    // }
    // fn insert(&mut self, block: &str) -> Result<(), ParseError> {
    //     dbg!(block);
    //     // let parser = regex!(r"^(\d+)$");
    //     // let segment = parser.captures(block).ok_or(ParseError)?;
    //     // self.line.push(segment[1].parse::<_>());
    //     Ok(())
    // }
    fn end_of_data(&mut self) {
        dbg!(&self.line);
    }
    fn part1(&mut self) -> Self::Output1 {
        1
    }
    fn part2(&mut self) -> Self::Output2 {
        2
    }
}
