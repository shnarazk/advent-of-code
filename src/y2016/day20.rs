//! <https://adventofcode.com/2016/day/20>
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
pub struct Puzzle {
    line: Vec<(usize, usize)>,
}

#[aoc(2016, 20)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        let input = line_parser::to_usizes(block, '-')?;
        self.line.push((input[0], input[1]));
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut result = usize::MAX;
        let mut vals: Vec<usize> = Vec::new();
        for (l, h) in self.line.iter() {
            vals.push(*l);
            vals.push(*h);
        }
        vals.sort_unstable();
        for p in vals.iter() {
            for x in [p.saturating_sub(1), p + 1] {
                if self.line.iter().all(|(l, h)| x < *l || *h < x) {
                    result = result.min(x);
                }
            }
        }
        result
    }
    fn part2(&mut self) -> Self::Output2 {
        0
    }
}

#[cfg(feature = "y2016")]
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
