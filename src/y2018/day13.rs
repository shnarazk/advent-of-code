//! <https://adventofcode.com/2018/day/13>
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

type Dim2 = (isize, isize);

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Cart {
    clockwise: bool,
    location: Dim2,
    direction: Dim2,
}

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Vec<u8>>,
    cart: Vec<Cart>,
}

#[aoc(2018, 13)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.line
            .push(block.chars().map(|c| c as u8).collect::<Vec<u8>>());
        Ok(())
    }
    fn after_insert(&mut self) {
        for (y, l) in self.line.iter_mut().enumerate() {
            for (x, c) in l.iter_mut().enumerate() {
                match c {
                    b'<' => {
                        self.cart.push(Cart {
                            clockwise: false,
                            location: (y as isize, x as isize),
                            direction: (0, -1),
                        });
                        *c = b'-';
                    }
                    b'>' => {
                        self.cart.push(Cart {
                            clockwise: true,
                            location: (y as isize, x as isize),
                            direction: (0, 1),
                        });
                        *c = b'-';
                    }
                    b'^' => {
                        self.cart.push(Cart {
                            clockwise: false,
                            location: (y as isize, x as isize),
                            direction: (-1, 0),
                        });
                        *c = b'|';
                    }
                    b'v' => {
                        self.cart.push(Cart {
                            clockwise: true,
                            location: (y as isize, x as isize),
                            direction: (1, 0),
                        });
                        *c = b'|';
                    }
                    _ => (),
                }
            }
        }
        dbg!(self.cart.len());
    }
    fn part1(&mut self) -> Self::Output1 {
        0
    }
    fn part2(&mut self) -> Self::Output2 {
        0
    }
}
