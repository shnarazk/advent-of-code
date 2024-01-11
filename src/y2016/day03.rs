//! <https://adventofcode.com/2016/day/03>
use crate::{
    framework::{aoc, AdventOfCode, ParseError},
    regex,
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Vec<usize>>,
}

#[aoc(2016, 3)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        let parser = regex!(r"^ +([0-9]+) +([0-9]+) +([0-9]+)$");
        let segment = parser.captures(block).ok_or(ParseError)?;
        self.line.push(vec![
            segment[1].parse::<usize>()?,
            segment[2].parse::<usize>()?,
            segment[3].parse::<usize>()?,
        ]);
        Ok(())
    }
    fn end_of_data(&mut self) {
        // dbg!(&self.line);
    }
    fn part1(&mut self) -> Self::Output1 {
        self.line
            .iter()
            .filter(|vec| {
                let mut v: Vec<usize> = vec.to_vec();
                v.sort_unstable();
                v[2] < v[0] + v[1]
            })
            .count()
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut count = 0;
        for j in 0..self.line.len() / 3 {
            for i in 0..3 {
                let mut v = [
                    self.line[j * 3][i],
                    self.line[j * 3 + 1][i],
                    self.line[j * 3 + 2][i],
                ];
                v.sort_unstable();
                if v[2] < v[0] + v[1] {
                    count += 1;
                }
            }
        }
        count
    }
}
