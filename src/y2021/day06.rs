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
        Ok(DataSegment {
            vec: s
                .split(',')
                .map(|i| {
                    i.strip_suffix('\n')
                        .unwrap_or(i)
                        .parse::<usize>()
                        .expect("bad num")
                })
                .collect::<Vec<usize>>(),
        })
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
    // handle header
    // fn header(&mut self, input: &str) -> Maybe<Option<String>> {
    //     let parser: Regex = Regex::new(r"^(.+)\n\n((.|\n)+)$").expect("wrong");
    //     let segment = parser.captures(input).ok_or(ParseError)?;
    //     for num in segment[1].split(',') {
    //         let _value = num.parse::<usize>()?;
    //     }
    //     Ok(Some(segment[2].to_string()))
    // }
    /// add a data block
    fn insert(&mut self, object: Self::Segment) {
        self.vec = object.vec;
    }
    // finalize
    // fn after_insert(&mut self) {}
    /// solver for part1
    fn part1(&mut self) -> usize {
        let mut vec = self.vec.clone();
        for _ in 0..80 {
            go_forward(&mut vec);
        }
        vec.len()
    }
    /// solver for part2
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
