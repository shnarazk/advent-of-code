//! <https://adventofcode.com/2019/day/12>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::neighbors,
        regex,
    },
    std::collections::HashMap,
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<[isize; 6]>,
}

#[aoc(2019, 12)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        let parser = regex!(r" *<x=(-?\d+), y=(-?\d+), z=(-?\d+)>");
        let segment = parser.captures(block).ok_or(ParseError)?;
        self.line.push([
            segment[1].parse::<isize>().unwrap(),
            segment[2].parse::<isize>().unwrap(),
            segment[3].parse::<isize>().unwrap(),
            0,
            0,
            0,
        ]);
        Ok(())
    }
    fn after_insert(&mut self) {
        dbg!(&self.line);
    }
    fn part1(&mut self) -> Self::Output1 {
        for _ in 0..1000 {
            let mut delta = Vec::new();
            for _ in self.line.iter() {
                delta.push([0; 3]);
            }
            // calculate gravities
            for i in 0..self.line.len() {
                for j in i + 1..self.line.len() {
                    for axis in 0..3 {
                        let d = (self.line[j][axis] - self.line[i][axis]).signum();
                        delta[i][axis] += d;
                        delta[j][axis] -= d;
                    }
                }
            }
            // update the velocities by applying gravity
            for (i, moon) in self.line.iter_mut().enumerate() {
                for (axis, m) in moon.iter_mut().skip(3).enumerate() {
                    *m += delta[i][axis];
                    delta[i][axis] = 0;
                }
            }
            // update the positions
            for moon in self.line.iter_mut() {
                for axis in 0..3 {
                    moon[axis] += moon[axis + 3];
                }
            }
        }
        // calculate energy
        let mut total: usize = 0;
        for moon in self.line.iter() {
            let mut potential: usize = 0;
            let mut kinetic: usize = 0;
            for axis in 0..3 {
                potential += moon[axis].unsigned_abs();
                kinetic += moon[axis + 3].unsigned_abs();
            }
            total += potential * kinetic;
        }
        total
    }
    fn part2(&mut self) -> Self::Output2 {
        0
    }
}

#[cfg(feature = "y2019")]
#[cfg(test)]
mod test {
    use {
        super::*,
        crate::framework::{Answer, Description},
    };

    // #[test]
    // fn test_part1() {
    //     assert_eq!(
    //         Puzzle::solve(Description::TestData("".to_string()), 1),
    //         Answer::Part1(0)
    //     );
    // }
}
