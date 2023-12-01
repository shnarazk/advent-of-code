//! <https://adventofcode.com/2015/day/3>
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        line_parser,
    },
    std::collections::HashMap,
};

#[derive(Debug, Default)]
pub struct Puzzle {
    line: Vec<char>,
    hash: HashMap<(isize, isize), usize>,
}

#[aoc(2015, 3)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.line = line_parser::to_chars(block)?;
        Ok(())
    }
    fn end_of_data(&mut self) {
        // dbg!(&self.line);
    }
    fn part1(&mut self) -> Self::Output1 {
        self.hash.insert((0, 0), 1);
        let mut pos: (isize, isize) = (0, 0);
        for c in self.line.iter() {
            match *c {
                '^' => pos.0 -= 1,
                'v' => pos.0 += 1,
                '<' => pos.1 -= 1,
                '>' => pos.1 += 1,
                _ => panic!(),
            }
            *self.hash.entry(pos).or_insert(0) += 1;
        }
        self.hash.len()
    }
    fn part2(&mut self) -> Self::Output2 {
        self.hash.insert((0, 0), 1);
        let mut pos: (isize, isize) = (0, 0);
        for (_, c) in self.line.iter().enumerate().filter(|(i, _)| i % 2 == 0) {
            match *c {
                '^' => pos.0 -= 1,
                'v' => pos.0 += 1,
                '<' => pos.1 -= 1,
                '>' => pos.1 += 1,
                _ => panic!(),
            }
            *self.hash.entry(pos).or_insert(0) += 1;
        }
        let mut pos: (isize, isize) = (0, 0);
        for (_, c) in self.line.iter().enumerate().filter(|(i, _)| i % 2 == 1) {
            match *c {
                '^' => pos.0 -= 1,
                'v' => pos.0 += 1,
                '<' => pos.1 -= 1,
                '>' => pos.1 += 1,
                _ => panic!(),
            }
            *self.hash.entry(pos).or_insert(0) += 1;
        }
        self.hash.len()
    }
}

#[cfg(feature = "y2015")]
#[cfg(test)]
mod test {
    use {
        super::*,
        crate::framework::{Answer, Description},
    };

    #[test]
    fn test_part1() {
        assert_eq!(
            Puzzle::solve(Description::TestData(">".to_string()), 1),
            Answer::Part1(2)
        );
        assert_eq!(
            Puzzle::solve(Description::TestData("^>v<".to_string()), 1),
            Answer::Part1(4)
        );
        assert_eq!(
            Puzzle::solve(Description::TestData("^v^v^v^v^v".to_string()), 1),
            Answer::Part1(2)
        );
    }
}
