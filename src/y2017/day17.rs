//! <https://adventofcode.com/2017/day/17>
use crate::framework::{aoc, AdventOfCode, ParseError};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: usize,
}

#[aoc(2017, 17)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.line = block.parse::<usize>()?;
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        let step = self.line;
        let mut ring: Vec<usize> = vec![0];
        let mut pos = 0;
        for i in 1..=2017 {
            pos = (step + pos) % ring.len();
            if pos == ring.len() - 1 {
                ring.push(i);
            } else {
                ring.insert(pos + 1, i);
            }
            pos += 1;
            // if pos == 1 {
            //     println!("{i:>6} {:?}", &ring[0..ring.len().min(20)]);
            // }
        }
        ring[(pos + 1) % ring.len()]
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut at_pos_1 = 0;
        let step = self.line;
        let mut pos = 0;
        for i in 1..=50_000_000 {
            pos = (step + pos) % i + 1;
            if pos == 1 {
                at_pos_1 = i;
            }
        }
        at_pos_1
    }
}
