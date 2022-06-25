//! <https://adventofcode.com/2019/day/3>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]

use std::collections::HashSet;
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::neighbors,
        line_parser, regex,
    },
    std::collections::HashMap,
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Vec<(isize, isize)>>,
}

#[aoc(2019, 3)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        // dbg!(&block);
        let parser = regex!(r"^([URDL])(\d+)");
        let mut vec = Vec::new();
        for segment in block.split(',') {
            if let Some(seg) = parser.captures(segment) {
                match (&seg[1], seg[2].parse::<isize>()) {
                    ("U", Ok(d)) => vec.push((-d, 0)),
                    ("D", Ok(d)) => vec.push((d, 0)),
                    ("L", Ok(d)) => vec.push((0, -d)),
                    ("R", Ok(d)) => vec.push((0, d)),
                    _ => panic!(),
                }
            }
        }
        self.line.push(vec);
        Ok(())
    }
    fn after_insert(&mut self) {
        // dbg!(&self.line);
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut checked: HashSet<(isize, isize)> = HashSet::new();
        let mut oy = 0;
        let mut ox = 0;
        for (dy, dx) in self.line[0].iter() {
            for y in 0.min(*dy)..=0.max(*dy) {
                for x in 0.min(*dx)..=0.max(*dx) {
                    checked.insert((oy + y, ox + x));
                }
            }
            oy += dy;
            ox += dx;
        }
        dbg!(checked.len());
        let mut lowest = usize::MAX / 4;
        oy = 0;
        ox = 0;
        checked.remove(&(0, 0));
        for (dy, dx) in self.line[1].iter() {
            for y in 0.min(*dy)..=0.max(*dy) {
                for x in 0.min(*dx)..=0.max(*dx) {
                    let py = oy + y;
                    let px = ox + x;
                    if checked.contains(&(py, px)) && (py.abs() + px.abs()) < (lowest as isize) {
                        lowest = (py.abs() + px.abs()) as usize;
                    }
                }
            }
            oy += dy;
            ox += dx;
        }
        dbg!(lowest)
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
