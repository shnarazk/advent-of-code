//! <https://adventofcode.com/2019/day/4>
use crate::{
    framework::{AdventOfCode, ParseError, aoc},
    parser,
};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<usize>,
}

#[aoc(2019, 4)]
impl AdventOfCode for Puzzle {
    fn prepare(&mut self, input: &str) -> Result<(), ParseError> {
        self.line = parser::to_usizes(input, &['-'])?;
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut count = 0;
        for i in self.line[0]..=self.line[1] {
            let s = format!("{i}").chars().map(|c| c as u8).collect::<Vec<u8>>();
            if s.windows(2).any(|v| v[0] == v[1]) && s.windows(2).all(|v| v[0] <= v[1]) {
                count += 1;
            }
        }
        count
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut count = 0;
        for i in self.line[0]..=self.line[1] {
            let s = format!("{i}").chars().map(|c| c as u8).collect::<Vec<u8>>();
            let mut ch = b' ';
            let mut cnt = 1;
            for c in s.iter() {
                if ch == *c {
                    cnt += 1;
                } else if cnt == 2 {
                    break;
                } else {
                    ch = *c;
                    cnt = 1;
                }
            }
            if cnt != 2 {
                continue;
            }
            if s.windows(2).all(|v| v[0] <= v[1]) {
                count += 1;
            }
        }
        count
    }
}
