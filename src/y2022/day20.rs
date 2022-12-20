//! <https://adventofcode.com/2022/day/20>
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
    line: Vec<isize>,
}

#[aoc_at(2022, 20)]
impl AdventOfCode for Puzzle {
    type Output1 = isize;
    type Output2 = isize;
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.line.push(block.parse::<isize>()?);
        Ok(())
    }
    fn after_insert(&mut self) {
        let mut count: HashMap<isize, usize> = HashMap::new();
        for n in self.line.iter() {
            *count.entry(*n).or_insert(0) += 1;
        }
        dbg!(count.get(&0));
        // assert!(count.values().all(|c| *c == 1));
        dbg!(&self.line.len());
    }
    fn part1(&mut self) -> Self::Output1 {
        let len = self.line.len();
        let mut next: Vec<usize> = self
            .line
            .iter()
            .enumerate()
            .map(|(i, _)| (i + 1) % len)
            .collect::<Vec<usize>>();
        let mut prev: Vec<usize> = self
            .line
            .iter()
            .enumerate()
            .map(|(i, _)| (i + len - 1) % len)
            .collect::<Vec<usize>>();
        // self.print(&next);
        assert!(self.is_sound(&next), "0");
        for n in 0..self.line.len() {
            self.shift(&mut next, &mut prev, n);
            // self.print(&next);
            // let mut check = next.clone();
            // check.sort();
            // let cal = (0..len).collect::<Vec<usize>>();
            // assert_eq!(check, cal);
            // assert!(self.is_sound(&next), "{n}");
        }
        // self.print(&next);
        self.value(&next)
    }
    fn part2(&mut self) -> Self::Output2 {
        2
    }
}

impl Puzzle {
    fn shift(&self, next: &mut [usize], prev: &mut [usize], i: usize) {
        let len = self.line.len();
        let val = self.line[i];
        let mut j = i;
        match val.signum() {
            0 => (),
            1 => {
                for _ in 0..val.unsigned_abs() {
                    j = next[j];
                    // To understand the following, I needed to cheak
                    if j == i {
                        j = next[j];
                    }
                }
            }
            -1 => {
                for _ in 0..(val.unsigned_abs() + 1) {
                    j = prev[j];
                    if j == i {
                        j = prev[j];
                    }
                }
            }
            _ => unreachable!(),
        }
        // println!(
        //     "{} moves between {} and {}:",
        //     self.line[i], self.line[j], self.line[next[j]]
        // );
        let prev_i = prev[i];
        let next_i = next[i];
        let next_j = next[j];
        if j == i || next_j == i {
            dbg!(i, val);
            return;
        }

        assert_ne!(i, j);
        assert_ne!(i, next_i);
        assert_ne!(i, prev_i);
        next[prev_i] = next_i;
        next[j] = i;
        next[i] = next_j;

        prev[next_j] = i;
        prev[i] = j;
        prev[next_i] = prev_i;
    }
    fn print(&self, next: &[usize]) {
        let mut i = 0;
        loop {
            print!("{}, ", self.line[i]);
            i = next[i];
            if i == 0 {
                break;
            }
        }
        println!();
    }
    fn value(&self, next: &[usize]) -> isize {
        let Some((mut i, _)) = self.line.iter().enumerate().find(|(_, i)| **i == 0) else {
            panic!();
        };
        let mut count = 0;
        let mut val = 0;
        loop {
            count += 1;
            i = next[i];
            if [1000, 2000, 3000].contains(&count) {
                val += dbg!(self.line[i]);
                if count == 3000 {
                    return val;
                }
            }
        }
    }
    fn is_sound(&self, next: &[usize]) -> bool {
        let Some((mut i, _)) = self.line.iter().enumerate().find(|(_, i)| **i == 0) else {
            panic!();
        };
        for _ in 0..self.line.len() {
            i = next[i];
        }
        self.line[i] == 0
    }
}
