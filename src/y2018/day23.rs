//! <https://adventofcode.com/2018/day/23>
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

trait Geometry {
    fn x(&self) -> isize;
    fn y(&self) -> isize;
    fn z(&self) -> isize;
    fn dist(&self, other: &Self) -> usize;
}

type Dim3 = (isize, isize, isize);

impl Geometry for Dim3 {
    fn x(&self) -> isize {
        self.0
    }
    fn y(&self) -> isize {
        self.1
    }
    fn z(&self) -> isize {
        self.2
    }
    fn dist(&self, other: &Dim3) -> usize {
        (self.0 - other.0).unsigned_abs()
            + (self.1 - other.1).unsigned_abs()
            + (self.2 - other.2).unsigned_abs()
    }
}

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<(Dim3, usize)>,
}

#[aoc(2018, 23)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        let parser = regex!(r"^pos=<(-?\d+),(-?\d+),(-?\d+)>, r=(-?\d+)$");
        let segment = parser.captures(block).ok_or(ParseError)?;
        self.line.push((
            (
                segment[1].parse::<isize>()?,
                segment[2].parse::<isize>()?,
                segment[3].parse::<isize>()?,
            ),
            segment[4].parse::<usize>()?,
        ));
        Ok(())
    }
    fn after_insert(&mut self) {
        dbg!(self.line.len());
    }
    fn part1(&mut self) -> Self::Output1 {
        let strongest: (&usize, &Dim3) = self.line.iter().map(|(p, r)| (r, p)).max().unwrap();
        let n: usize = self
            .line
            .iter()
            .filter(|(p, r)| strongest.1.dist(p) <= *strongest.0)
            .count();
        n
    }
    fn part2(&mut self) -> Self::Output2 {
        0
    }
}
