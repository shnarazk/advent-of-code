//! <https://adventofcode.com/2016/day/23>
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

#[derive(Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Val {
    Reg(u8),
    Lit(isize),
}

#[derive(Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Code {
    Cpy(Val, Val),
    Inc(Val),
    Dec(Val),
    Jnz(Val, Val),
    Tgl(Val),
}

#[derive(Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Code>,
}

#[aoc(2016, 23)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        let parse_val = |s: &str| {
            let c: char = s.chars().next().unwrap();
            if c.is_ascii_alphabetic() {
                Val::Reg(c as u8 - b'a')
            } else {
                Val::Lit(s.parse::<isize>().unwrap())
            }
        };
        if let Ok(code) = regex!(r"^cpy ([a-z]|-?\d+) ([a-z]|-?\d+)$")
            .captures(block)
            .ok_or(ParseError)
        {
            self.line
                .push(Code::Cpy(parse_val(&code[1]), parse_val(&code[2])));
        } else if let Ok(code) = regex!(r"^inc ([a-z]|-?\d+)$")
            .captures(block)
            .ok_or(ParseError)
        {
            self.line.push(Code::Inc(parse_val(&code[1])));
        } else if let Ok(code) = regex!(r"^dec ([a-z]|-?\d+)$")
            .captures(block)
            .ok_or(ParseError)
        {
            self.line.push(Code::Dec(parse_val(&code[1])));
        } else if let Ok(code) = regex!(r"^jnz ([a-z]|-?\d+) ([a-z]|-?\d+)$")
            .captures(block)
            .ok_or(ParseError)
        {
            self.line
                .push(Code::Jnz(parse_val(&code[1]), parse_val(&code[2])));
        } else if let Ok(code) = regex!(r"^tgl ([a-z]|-?\d+)$")
            .captures(block)
            .ok_or(ParseError)
        {
            self.line.push(Code::Tgl(parse_val(&code[1])));
        }
        Ok(())
    }
    fn after_insert(&mut self) {
        // dbg!(&self.line);
    }
    fn part1(&mut self) -> Self::Output1 {
        0
    }
    fn part2(&mut self) -> Self::Output2 {
        0
    }
}
