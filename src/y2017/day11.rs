//! <https://adventofcode.com/2017/day/11>
use crate::framework::{aoc, AdventOfCode, ParseError};

#[derive(Debug, Eq, Hash, PartialEq)]
enum Direction {
    N,
    NE,
    SE,
    S,
    SW,
    NW,
}

impl TryFrom<&str> for Direction {
    type Error = ();
    fn try_from(value: &str) -> Result<Self, Self::Error> {
        match value {
            "n" => Ok(Direction::N),
            "ne" => Ok(Direction::NE),
            "se" => Ok(Direction::SE),
            "s" => Ok(Direction::S),
            "sw" => Ok(Direction::SW),
            "nw" => Ok(Direction::NW),
            _ => Err(()),
        }
    }
}

impl Direction {
    fn dir(&self) -> (isize, isize) {
        match self {
            Direction::N => (1, 1),
            Direction::NE => (1, 0),
            Direction::SE => (0, -1),
            Direction::S => (-1, -1),
            Direction::SW => (-1, 0),
            Direction::NW => (0, 1),
        }
    }
}

#[derive(Debug, Default, Eq, Hash, PartialEq)]
pub struct Puzzle {
    line: Vec<Direction>,
}

#[aoc(2017, 11)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.line = block
            .split(',')
            .map(|s| Direction::try_from(s).expect("parse error"))
            .collect::<Vec<_>>();
        Ok(())
    }
    fn wrap_up(&mut self) {
        dbg!(&self.line.len());
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut dir: (isize, isize) = (0, 0);
        for d in self.line.iter() {
            let (ne, nw) = d.dir();
            dir.0 += ne;
            dir.1 += nw;
        }
        // canelling opposite pairs
        let ne = dir.0.unsigned_abs();
        let nw = dir.1.unsigned_abs();
        if dir.0.signum() == dir.1.signum() {
            ne + nw - ne.min(nw)
        } else {
            ne + nw
        }
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut max_dist = 0;
        let mut dir: (isize, isize) = (0, 0);
        for d in self.line.iter() {
            let (ne, nw) = d.dir();
            dir.0 += ne;
            dir.1 += nw;
            let tmp = {
                let ne = dir.0.unsigned_abs();
                let nw = dir.1.unsigned_abs();
                if dir.0.signum() == dir.1.signum() {
                    ne + nw - ne.min(nw)
                } else {
                    ne + nw
                }
            };
            max_dist = max_dist.max(tmp);
        }
        max_dist
    }
}
