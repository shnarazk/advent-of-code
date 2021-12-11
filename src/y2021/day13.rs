#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use crate::{
    framework::{aoc_at, AdventOfCode, Maybe, ParseError},
    line_parser,
};
use lazy_static::lazy_static;
use regex::Regex;
use std::collections::HashMap;

#[derive(Debug, Default, PartialEq)]
pub struct Puzzle {
    line: Vec<()>,
}

#[aoc_at(2021, 13)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    // fn header(&mut self, input: String) -> Maybe<Option<String>> {
    //     let parser: Regex = Regex::new(r"^(.+)\n\n((.|\n)+)$").expect("wrong");
    //     let segment = parser.captures(input).ok_or(ParseError)?;
    //     for num in segment[1].split(',') {
    //         let _value = num.parse::<usize>()?;
    //     }
    //     Ok(Some(segment[2].to_string()))
    // }
    fn insert(&mut self, block: &str) -> Maybe<()> {
        lazy_static! {
            static ref PARSER: Regex = Regex::new(r"^([0-9]+)$").expect("wrong");
        }
        let segment = PARSER.captures(block).ok_or(ParseError)?;
        // self.line.push(object);
        Ok(())
    }
    // fn after_insert(&mut self) {}
    fn part1(&mut self) -> Self::Output1 {
        0
    }
    fn part2(&mut self) -> Self::Output2 {
        0
    }
}
