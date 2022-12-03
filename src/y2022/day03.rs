//! <https://adventofcode.com/2022/day/3>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::neighbors,
        line_parser, regex,
    },
    std::collections::HashMap,
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<(Vec<u8>, Vec<u8>)>,
}

#[aoc(2022, 3)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        let v = block.chars().map(|c| c as u8).collect::<Vec<u8>>();
        let len = v.len();
        self.line
            .push((v[0..len / 2].to_vec(), v[len / 2..len].to_vec()));
        // println!(
        //     "{}({}) => {}, {}",
        //     block,
        //     len,
        //     v[0..len / 2].iter().map(|c| *c as char).collect::<String>(),
        //     v[len / 2..len]
        //         .iter()
        //         .map(|c| *c as char)
        //         .collect::<String>(),
        // );
        Ok(())
    }
    fn after_insert(&mut self) {
        // dbg!(&self.line);
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut count = 0;
        for l in self.line.iter() {
            for c in l.0.iter() {
                if l.1.contains(c) {
                    count += if *c <= b'Z' {
                        (*c - b'A') as usize + 27
                    } else {
                        (*c - b'a') as usize + 1
                    };
                    break;
                }
            }
        }
        count
    }
    fn part2(&mut self) -> Self::Output2 {
        0
    }
}
