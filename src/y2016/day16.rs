//! <https://adventofcode.com/2016/day/16>
use crate::framework::{AdventOfCode, ParseError, aoc_at};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<bool>,
}

#[aoc_at(2016, 16)]
impl AdventOfCode for Puzzle {
    type Output1 = String;
    type Output2 = String;
    fn prepare(&mut self, _: &str) -> Result<(), ParseError> {
        self.line = "10001110011110000"
            .chars()
            .map(|c| c == '1')
            .collect::<Vec<_>>();
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        let disk_size = 272;
        let mut d = self.line.clone();
        while d.len() < disk_size {
            d = lengthen(d);
        }
        checksum(disk_size, &d)
            .iter()
            .map(|b| if *b { '1' } else { '0' })
            .collect::<String>()
    }
    fn part2(&mut self) -> Self::Output2 {
        let disk_size = 35651584;
        let mut d = self.line.clone();
        while d.len() < disk_size {
            d = lengthen(d);
        }
        checksum(disk_size, &d)
            .iter()
            .map(|b| if *b { '1' } else { '0' })
            .collect::<String>()
    }
}

fn lengthen(mut a: Vec<bool>) -> Vec<bool> {
    let mut b: Vec<bool> = a.iter().map(|b| !*b).collect::<Vec<_>>();
    b.reverse();
    a.push(false);
    a.append(&mut b);
    a
}

fn checksum(length: usize, data: &[bool]) -> Vec<bool> {
    let mut result = data.to_vec();
    let mut len = length / 2;
    loop {
        result = (0..len)
            .map(|i| result[2 * i] == result[2 * i + 1])
            .collect::<Vec<_>>();
        if result.len() % 2 == 1 {
            return result;
        }
        len /= 2;
    }
}
