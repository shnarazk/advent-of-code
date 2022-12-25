//! <https://adventofcode.com/2022/day/25>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{aoc_at, AdventOfCode, ParseError},
        geometric::neighbors,
        line_parser, regex,
    },
    std::collections::HashMap,
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Vec<isize>>,
}

#[aoc_at(2022, 25)]
impl AdventOfCode for Puzzle {
    type Output1 = String;
    type Output2 = usize;
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.line.push(
            block
                .chars()
                .map(|c| match c {
                    '-' => -1,
                    '=' => -2,
                    '0' => 0,
                    '1' => 1,
                    '2' => 2,
                    '3' => 3,
                    _ => unreachable!(),
                })
                .collect::<Vec<isize>>(),
        );
        Ok(())
    }
    fn after_insert(&mut self) {
        dbg!(&self.line.len());
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut sum: usize = self
            .line
            .iter()
            .map(|n| {
                let v = n
                    .iter()
                    .rev()
                    .enumerate()
                    .fold(0, |acc, (i, k)| acc + k * 5_isize.pow(i as u32))
                    as usize;
                dbg!(v)
            })
            .sum();
        dbg!(sum);
        let mut buffer: Vec<char> = Vec::new();
        while 0 < sum {
            let digit = sum % 5;
            sum /= 5;
            let ch = match digit {
                0 => '0',
                1 => '1',
                2 => '2',
                3 => {
                    sum += 1;
                    '='
                }
                4 => {
                    sum += 1;
                    '-'
                }
                _ => unreachable!(),
            };
            buffer.push(ch);
        }
        buffer.reverse();
        buffer.iter().collect::<String>()
    }
    fn part2(&mut self) -> Self::Output2 {
        2
    }
}
