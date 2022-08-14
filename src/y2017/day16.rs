//! <https://adventofcode.com/2017/day/16>
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

#[derive(Debug, Eq, PartialEq)]
enum Dance {
    Spin(usize),
    Exchange(usize, usize),
    Partner(usize, usize),
}

impl TryFrom<&str> for Dance {
    type Error = ParseError;
    fn try_from(value: &str) -> Result<Self, Self::Error> {
        fn to_16(val: &str) -> Result<usize, ParseError> {
            if let Some(c) = val.chars().next() {
                Ok(((c as u8) - b'a') as usize)
            } else {
                Err(ParseError)
            }
        }
        let spin = regex!(r"^s(\d+)");
        let exchange = regex!(r"^x(\d+)/(\d+)$");
        let partner = regex!(r"^p([a-p])/([a-p])$");
        if let Some(segment) = spin.captures(value) {
            Ok(Dance::Spin(segment[1].parse::<usize>()?))
        } else if let Some(segment) = exchange.captures(value) {
            Ok(Dance::Exchange(
                segment[1].parse::<usize>()?,
                segment[2].parse::<usize>()?,
            ))
        } else if let Some(segment) = partner.captures(value) {
            Ok(Dance::Partner(to_16(&segment[1])?, to_16(&segment[2])?))
        } else {
            Err(ParseError)
        }
    }
}

#[derive(Debug, Default, Eq, PartialEq)]
pub struct Puzzle {
    line: Vec<Dance>,
}

#[aoc(2017, 16)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        for seg in block.split(',') {
            self.line.push(Dance::try_from(seg)?);
        }
        Ok(())
    }
    fn after_insert(&mut self) {
        dbg!(&self.line.len());
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut list = (0..16).collect::<Vec<_>>();
        let mut work = list.clone();
        let len = list.len();
        for mv in self.line.iter() {
            match mv {
                Dance::Spin(x) => {
                    for i in 0..list.len() {
                        work[(i + x) % len] = list[i];
                    }
                    std::mem::swap(&mut list, &mut work);
                }

                Dance::Exchange(x, y) => {
                    list.swap(*x, *y);
                }
                Dance::Partner(x, y) => {
                    let mut xi = 0;
                    let mut yi = 0;
                    for (i, v) in list.iter().enumerate() {
                        if v == x {
                            xi = i;
                        } else if v == y {
                            yi = i;
                        }
                    }
                    list.swap(xi, yi);
                }
            }
        }
        println!(
            "{}",
            list.iter()
                .map(|c| ((*c as u8) + b'a') as char)
                .collect::<String>()
        );
        0
    }
    fn part2(&mut self) -> Self::Output2 {
        0
    }
}
