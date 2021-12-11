#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use crate::{aoc_at, AdventOfCode, Description, Maybe, ParseError};
use lazy_static::lazy_static;
use regex::Regex;
use std::collections::HashMap;

#[derive(Debug, PartialEq)]
struct Puzzle {}

#[aoc_at(2021, 16)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn default() -> Self {
        Self {}
    }
    // handle header
    // fn header(&mut self, input: String) -> Maybe<Option<String>> {
    //     let parser: Regex = Regex::new(r"^(.+)\n\n((.|\n)+)$").expect("wrong");
    //     let segment = parser.captures(input).ok_or(ParseError)?;
    //     for num in segment[1].split(',') {
    //         let _value = num.parse::<usize>()?;
    //     }
    //     Ok(Some(segment[2].to_string()))
    // }
    /// add a data block
    fn insert(&mut self, block: &str) -> Maybe<()> {
        lazy_static! {
            static ref PARSER: Regex = Regex::new(r"^([0-9]+)$").expect("wrong");
        }
        let segment = PARSER.captures(block).ok_or(ParseError)?;
        // self.line.push(object);
        Ok(())
    }
    // finalize
    // fn after_insert(&mut self) {}
    /// solver for part1
    fn part1(&mut self) -> usize {
        0
    }
    /// solver for part2
    fn part2(&mut self) -> usize {
        0
    }
}

pub fn go(part: usize, desc: Description) {
    dbg!(Puzzle::solve(&desc, part));
}
