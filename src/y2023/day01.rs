//! <https://adventofcode.com/2023/day/1>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]

use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::neighbors,
        line_parser, progress, regex,
    },
    std::collections::HashMap,
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Vec<char>>,
    line2: Vec<Vec<char>>,
}

#[aoc(2023, 1)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.line.push(block.chars().collect::<Vec<_>>());
        let mut b = block.to_owned();
        let subst = [
            ("one", '1'),
            ("two", '2'),
            ("three", '3'),
            ("four", '4'),
            ("five", '5'),
            ("six", '6'),
            ("seven", '7'),
            ("eight", '8'),
            ("nine", '9'),
        ];
        let mut acc: Vec<char> = Vec::new();
        'next_char: while !b.is_empty() {
            for (r, s) in subst {
                if b.starts_with(r) {
                    acc.push(s);
                    // b = b.strip_prefix(r).unwrap().to_string();
                    // Wow! letters can be overwapped!
                    let mut bs = b.chars();
                    let c = bs.next().unwrap();
                    b = bs.collect::<String>();
                    continue 'next_char;
                }
            }
            let mut bs = b.chars();
            let c = bs.next().unwrap();
            acc.push(c);
            b = bs.collect::<String>();
        }
        self.line2.push(acc);
        Ok(())
    }
    fn wrap_up(&mut self) {}
    fn part1(&mut self) -> Self::Output1 {
        self.line
            .iter()
            .map(|v| {
                let d = v.iter().filter(|c| c.is_digit(10)).collect::<Vec<_>>();
                vec![d[0], d[d.len() - 1]]
                    .into_iter()
                    .collect::<String>()
                    .parse::<usize>()
                    .unwrap()
            })
            .sum()
    }
    fn part2(&mut self) -> Self::Output2 {
        self.line2
            .iter()
            .map(|v| {
                let d = v.iter().filter(|c| c.is_digit(10)).collect::<Vec<_>>();
                vec![d[0], d[d.len() - 1]]
                    .into_iter()
                    .collect::<String>()
                    .parse::<usize>()
                    .unwrap()
            })
            .sum()
    }
}
