#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use crate::{AdventOfCode, Description, Maybe, ParseError, TryParse};
use lazy_static::lazy_static;
use regex::Regex;
use std::collections::HashMap;

#[derive(Debug, PartialEq)]
struct DataSegment {
    vec: Vec<usize>,
}

impl TryParse for DataSegment {
    /// make a `Object` from a string block
    fn parse(s: &str) -> Result<Self, ParseError> {
        let mut vec = Vec::new();
        for i in s.split(',') {
            vec.push(
                i.strip_suffix('\n')
                    .unwrap_or(i)
                    .parse::<usize>()
                    .map_err(|_| ParseError)?,
            );
        }
        Ok(DataSegment { vec })
    }
}

fn rotating_go_forward(acum: &mut [usize; 7], index: usize, pre1: &mut usize, pre2: &mut usize) {
    let matured = *pre2;
    *pre2 = *pre1;
    *pre1 = acum[index];
    acum[index] += matured;
}

fn go_forward(vec: &mut Vec<usize>) {
    let mut news = 0;
    for i in vec.iter_mut() {
        if *i == 0 {
            news += 1;
            *i = 6;
        } else {
            *i -= 1;
        }
    }
    for _ in 0..news {
        vec.push(8);
    }
}

#[derive(Debug, PartialEq)]
struct Puzzle {
    vec: Vec<usize>,
}

impl AdventOfCode for Puzzle {
    type Segment = DataSegment;
    type Output1 = usize;
    type Output2 = usize;
    const YEAR: usize = 2021;
    const DAY: usize = 6;
    const DELIMITER: &'static str = "\n";
    fn default() -> Self {
        Self { vec: Vec::new() }
    }
    fn insert(&mut self, object: Self::Segment) {
        self.vec = object.vec;
    }
    fn part1(&mut self) -> usize {
        let mut vec = self.vec.clone();
        for _ in 0..80 {
            go_forward(&mut vec);
        }
        vec.len()
    }
    fn part2(&mut self) -> usize {
        let mut acum = [0; 7];
        for i in self.vec.iter() {
            acum[*i] += 1;
        }
        dbg!(&acum);
        let mut pre1 = 0;
        let mut pre2 = 0;
        for i in 0..256 {
            rotating_go_forward(&mut acum, i % 7, &mut pre1, &mut pre2);
            // dbg!(acum.iter().sum::<usize>() + pre1 + pre2);
        }
        acum.iter().sum::<usize>() + pre1 + pre2
    }
}

pub fn go(part: usize, desc: Description) {
    dbg!(Puzzle::solve(&desc, part));
}
