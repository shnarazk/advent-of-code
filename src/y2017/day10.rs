//! <https://adventofcode.com/2017/day/10>
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
    line: Vec<usize>,
    strn: String,
}

#[aoc(2017, 10)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.line = line_parser::to_usizes(block, ',')?;
        self.strn = block.trim().to_string();
        Ok(())
    }
    fn after_insert(&mut self) {
        // dbg!(&self.line.len());
    }
    fn part1(&mut self) -> Self::Output1 {
        let m: usize = 256;
        let mut list = (0..m).collect::<Vec<_>>();
        let mut current_position = 0;
        for (skip_size, length) in self.line.iter().enumerate() {
            assert!(*length <= m);
            for j in 0..length / 2 {
                // println!(
                //     "length: {length}, swap: {} and {}",
                //     (current_position + j) % m,
                //     (current_position + length - j - 1) % m
                // );
                list.swap(
                    (current_position + j) % m,
                    (current_position + length - j - 1) % m,
                );
                assert_ne!(
                    (current_position + j) % m,
                    (current_position + length - j - 1) % m,
                );
            }
            current_position += length + skip_size;
            current_position %= m;
            // println!("{list:?}");
        }
        list[0] * list[1]
    }
    fn part2(&mut self) -> Self::Output2 {
        let m: usize = 256;
        let mut list = (0..m).collect::<Vec<_>>();

        // Proccessing length sequence
        // if you are given 1,2,3, you should convert it to
        // the ASCII codes for each character: 49,44,50,44,51.
        // if you are given 1,2,3, your final sequence of lengths
        // should be 49,44,50,44,51,17,31,73,47,23
        let lengths: Vec<usize> = {
            let mut list: Vec<usize> = self
                .strn
                .chars()
                .map(|c| c as u8 as usize)
                .collect::<Vec<_>>();
            let mut postfix = vec![17, 31, 73, 47, 23];
            list.append(&mut postfix);
            list
        };

        let mut current_position = 0;
        let mut skip_size = 0;
        for _ in 0..64 {
            for length in lengths.iter() {
                for j in 0..*length / 2 {
                    list.swap(
                        (current_position + j) % m,
                        (current_position + *length - j - 1) % m,
                    );
                    assert_ne!(
                        (current_position + j) % m,
                        (current_position + *length - j - 1) % m,
                    );
                }
                current_position += length + skip_size;
                current_position %= m;
                skip_size += 1;
            }
        }
        // compress to dense hash
        let mut result: Vec<usize> = Vec::new();
        let mut working: usize = 0;
        for (i, c) in list.iter().enumerate() {
            match i % 16 {
                0 => working = *c,
                15 => result.push(working ^ *c),
                _ => working ^= *c,
            }
        }
        assert_eq!(16, result.len());
        for i in result.iter() {
            print!("{}", &format!("{:#x}", i)[2..]);
        }
        println!();
        0
    }
}
