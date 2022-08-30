//! <https://adventofcode.com/2018/day/20>
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
struct Reg(Vec<u8>);

#[derive(Debug, Eq, Hash, PartialEq)]
enum Rege {
    Run(Reg),
    Branch(Vec<Rege>),
}

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<u8>,
}

fn parse_to_run(string: &[u8], start: usize) -> Result<(Reg, usize), ParseError> {
    let mut i = start;
    while let Some(c) = string.get(i) {
        if *c == b'(' || *c == b'|' {
            break;
        }
        i += 1;
    }
    Ok((Reg(string[start..i].to_vec()), i))
}

fn parse_to_branch(string: &[u8], start: usize) -> Result<(Rege, usize), ParseError> {
    let mut vec: Vec<Rege> = Vec::new();
    let mut i = start;
    if string.get(start) == Some(&b'(') {
        if let Ok((element, j)) = parse_to_branch(string, i) {
            vec.push(element);
            i = j;
        } else {
        }
    } else if let Ok((element, j)) = parse_to_run(string, i) {
        vec.push(Rege::Run(element));
        i = j;
    } else {
    }
    while let Some(c) = string.get(i) {
        match c {
            b'|' => {
                if let Ok((element, j)) = parse_to_branch(string, i + 1) {
                    vec.push(element);
                    i = j;
                }
            }
            b')' => {
                break;
            }
            _ => unreachable!(),
        }
    }
    Ok((Rege::Branch(vec), i + 1))
}

#[aoc(2018, 20)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.line = block.chars().map(|c| c as u8).collect::<Vec<u8>>();
        Ok(())
    }
    fn after_insert(&mut self) {
        dbg!(&self.line);
    }
    fn part1(&mut self) -> Self::Output1 {
        0
    }
    fn part2(&mut self) -> Self::Output2 {
        0
    }
}
