#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use crate::{AdventOfCode, Description, Maybe, ParseError, TryParse};
use lazy_static::lazy_static;
use regex::Regex;
use std::collections::HashMap;

#[derive(Debug, PartialEq)]
struct DataSegment(Vec<usize>);

impl TryParse for DataSegment {
    fn parse(s: &str) -> Result<Self, ParseError> {
        Ok(DataSegment(
            s.trim()
                .split(',')
                .map(|i| i.parse::<usize>().unwrap())
                .collect(),
        ))
    }
}

#[derive(Debug, PartialEq)]
struct Puzzle {
    config: Vec<usize>,
}

impl AdventOfCode for Puzzle {
    type Segment = DataSegment;
    type Output1 = usize;
    type Output2 = usize;
    const YEAR: usize = 2021;
    const DAY: usize = 7;
    const DELIMITER: &'static str = "\n";
    fn default() -> Self {
        Self { config: Vec::new() }
    }
    fn insert(&mut self, object: Self::Segment) {
        self.config = object.0;
    }
    fn part1(&mut self) -> usize {
        let vec = &self.config;
        let len: usize = *vec.iter().max().unwrap();
        let mut fmin: usize = vec.iter().sum::<usize>().pow(2);
        for pos in 0..=len {
            fmin = fmin.min(
                vec.iter()
                    .map(|i| (*i as isize - pos as isize).abs() as usize)
                    .sum(),
            );
        }
        fmin
    }
    fn part2(&mut self) -> usize {
        let vec = &self.config;
        let len: usize = *vec.iter().max().unwrap();
        let mut fuel_table: Vec<Option<usize>> = Vec::new();
        fuel_table.resize(len + 1, None);
        fuel_table[0] = Some(0);
        fn get(table: &mut Vec<Option<usize>>, n: usize) -> usize {
            if let Some(k) = table[n] {
                k
            } else {
                let v = n + get(table, n - 1);
                table[n] = Some(v);
                v
            }
        }
        let mut fmin: usize = vec.iter().sum::<usize>() * vec.len();
        for pos in 0..=len {
            fmin = fmin.min(
                vec.iter()
                    .map(|i| get(&mut fuel_table, (*i as isize - pos as isize).abs() as usize))
                    .sum(),
            );
        }
        fmin
    }
}

pub fn go(part: usize, desc: Description) {
    dbg!(Puzzle::solve(&desc, part));
}

#[cfg(test)]
mod test {
    use {
        super::*,
        crate::{Answer, Description},
    };

    #[test]
    fn test_part1() {
        const TEST1: &str = "0\n1\n2";
        assert_eq!(
            Puzzle::parse(&Description::TestData(TEST1.to_string()))
                .expect("-")
                .run(1),
            Answer::Part1(0)
        );
    }
}
