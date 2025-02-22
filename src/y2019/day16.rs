//! <https://adventofcode.com/2019/day/16>
use crate::framework::{AdventOfCode, ParseError, aoc};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<i32>,
}

#[aoc(2019, 16)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, input: &str) -> Result<(), ParseError> {
        self.line = input
            .trim()
            .chars()
            .map(|c| (c as u8 - b'0') as i32)
            .collect::<Vec<i32>>();
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        let base_pattern: Vec<i32> = vec![0, 1, 0, -1];
        let mut scratch = self.line.clone();
        for _ in 0..100 {
            for (j, x) in scratch.iter_mut().enumerate() {
                let mut result = 0;
                for (i, p) in self.line.iter().enumerate() {
                    let ptn = base_pattern[((i + 1) / (j + 1)) % 4];
                    result += p * ptn;
                    // print!("{ptn}, ");
                }
                // println!("{:?}", result);
                *x = result;
            }
            for (i, v) in scratch.iter().enumerate() {
                self.line[i] = (*v % 10).abs();
            }
            // println!("{:?}", &self.line);
        }
        // println!("{:?}", &self.line[0..8]);
        self.line.iter().take(8).fold(0, |sum, d| sum * 10 + *d) as usize
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut v = Vec::new();
        for _ in 0..10_000 {
            v.append(&mut self.line.clone());
        }
        let skip = v.iter().take(7).fold(0, |sum, d| sum * 10 + *d) as usize;
        debug_assert!(v.len() < 2 * skip);
        self.line.clear();
        for x in v.iter().skip(skip) {
            self.line.push(*x);
        }
        let len = self.line.len();
        v.truncate(len);
        for _repeat in 0..100 {
            let mut psum = 0;
            v.iter_mut().for_each(|p| *p = 0);
            for (i, n) in self.line.iter().enumerate().rev() {
                psum = (psum + n) % 10;
                v[i] = psum;
            }
            std::mem::swap(&mut self.line, &mut v);
        }
        self.line.iter().take(8).fold(0, |s, d| s * 10 + *d) as usize
    }
}
