//! <https://adventofcode.com/2021/day/11>
use crate::{
    framework::{AdventOfCode, ParseError, aoc},
    geometric, parser,
};

#[derive(Clone, Debug, Default)]
pub struct Puzzle {
    line: Vec<Vec<usize>>,
    height: usize,
    width: usize,
    step: usize,
}

impl Puzzle {
    fn progress(&mut self, flash: Vec<(usize, usize)>, mut total: usize) -> usize {
        let mut secondary: Vec<(usize, usize)> = Vec::new();
        if flash.is_empty() {
            debug_assert!(self.line.iter().all(|v| v.iter().all(|i| *i <= 9)));
            if self.step == 0 {
                // for v in self.line.iter() {
                //     for i in v.iter() {
                //         print!("{}", i);
                //     }
                //     println!();
                // }
                // println!();
                return total;
            }
            for (j, v) in self.line.iter_mut().enumerate() {
                for (i, p) in v.iter_mut().enumerate() {
                    if *p == 9 {
                        secondary.push((j, i));
                    }
                    *p += 1;
                }
            }
        }
        for (j, i) in flash.iter() {
            for (jj, ii) in geometric::neighbors8(*j, *i, self.height, self.width) {
                if self.line[jj][ii] == 9 {
                    secondary.push((jj, ii))
                }
                self.line[jj][ii] += 1;
            }
        }
        total += flash.len();
        if secondary.is_empty() {
            for v in self.line.iter_mut() {
                for i in v.iter_mut() {
                    if 9 < *i {
                        *i = 0;
                    }
                }
            }
            self.step -= 1;
        }
        // dbg!(self.step, flash.is_empty());
        self.progress(secondary, total)
    }

    fn progress_check(&mut self, flash: Vec<(usize, usize)>) -> usize {
        let mut secondary: Vec<(usize, usize)> = Vec::new();
        if flash.is_empty() {
            if self.line.iter().all(|v| v.iter().all(|i| *i == 0)) {
                return self.step;
            }
            for (j, v) in self.line.iter_mut().enumerate() {
                for (i, p) in v.iter_mut().enumerate() {
                    if *p == 9 {
                        secondary.push((j, i));
                    }
                    *p += 1;
                }
            }
        }
        for (j, i) in flash.iter() {
            for (jj, ii) in geometric::neighbors8(*j, *i, self.height, self.width) {
                if self.line[jj][ii] == 9 {
                    secondary.push((jj, ii))
                }
                self.line[jj][ii] += 1;
            }
        }
        if secondary.is_empty() {
            for v in self.line.iter_mut() {
                for i in v.iter_mut() {
                    if 9 < *i {
                        *i = 0;
                    }
                }
            }
            self.step += 1;
        }
        self.progress_check(secondary)
    }
}

#[aoc(2021, 11)]
impl AdventOfCode for Puzzle {
    fn prepare(&mut self, input: &str) -> Result<(), ParseError> {
        for l in input.lines() {
            self.line.push(parser::to_digits(l)?);
        }
        self.height = self.line.len();
        self.width = self.line[0].len();
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        self.step = 100;
        self.progress(Vec::new(), 0)
    }
    fn part2(&mut self) -> Self::Output2 {
        self.progress_check(Vec::new())
    }
}
