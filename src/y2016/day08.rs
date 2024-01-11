//! <https://adventofcode.com/2016/day/08>
use crate::{
    framework::{aoc, AdventOfCode, ParseError},
    regex,
};

#[derive(Debug, Eq, PartialEq)]
enum Op {
    Rect(usize, usize),
    RotateRow(usize, usize),
    RotateCol(usize, usize),
}

#[derive(Debug, Default, Eq, PartialEq)]
pub struct Puzzle {
    line: Vec<Op>,
}

#[aoc(2016, 8)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        let rect = regex!(r"rect (\d+)x(\d+)");
        if let Some(segment) = rect.captures(block) {
            self.line.push(Op::Rect(
                segment[1].parse::<usize>()?,
                segment[2].parse::<usize>()?,
            ));
            return Ok(());
        }
        let rot_row = regex!(r"rotate row y=(\d+) by (\d+)");
        if let Some(segment) = rot_row.captures(block) {
            self.line.push(Op::RotateRow(
                segment[1].parse::<usize>()?,
                segment[2].parse::<usize>()?,
            ));
            return Ok(());
        }
        let rot_col = regex!(r"rotate column x=(\d+) by (\d+)");
        if let Some(segment) = rot_col.captures(block) {
            self.line.push(Op::RotateCol(
                segment[1].parse::<usize>()?,
                segment[2].parse::<usize>()?,
            ));
            return Ok(());
        }
        Err(ParseError)
    }
    fn part1(&mut self) -> Self::Output1 {
        let height = 6;
        let width = 50;
        let mut display = [[false; 50]; 6];
        for op in self.line.iter() {
            match op {
                Op::Rect(w, h) => {
                    for l in display.iter_mut().take(*h) {
                        for p in l.iter_mut().take(*w) {
                            *p = true;
                        }
                    }
                }
                Op::RotateCol(x, d) => {
                    for _ in 0..*d {
                        let tmp = display[height - 1][*x];
                        for j in (1..height).rev() {
                            display[j][*x] = display[j - 1][*x];
                        }
                        display[0][*x] = tmp;
                    }
                }
                Op::RotateRow(y, d) => {
                    for _ in 0..*d {
                        let tmp = display[*y][width - 1];
                        for j in (1..width).rev() {
                            display[*y][j] = display[*y][j - 1];
                        }
                        display[*y][0] = tmp;
                    }
                }
            }
        }
        display
            .iter()
            .map(|l| l.iter().filter(|b| **b).count())
            .sum()
    }
    fn part2(&mut self) -> Self::Output2 {
        let height = 6;
        let width = 50;
        let mut display = [[false; 50]; 6];
        for op in self.line.iter() {
            match op {
                Op::Rect(w, h) => {
                    for l in display.iter_mut().take(*h) {
                        for p in l.iter_mut().take(*w) {
                            *p = true;
                        }
                    }
                }
                Op::RotateCol(x, d) => {
                    for _ in 0..*d {
                        let tmp = display[height - 1][*x];
                        for j in (1..height).rev() {
                            display[j][*x] = display[j - 1][*x];
                        }
                        display[0][*x] = tmp;
                    }
                }
                Op::RotateRow(y, d) => {
                    for _ in 0..*d {
                        let tmp = display[*y][width - 1];
                        for j in (1..width).rev() {
                            display[*y][j] = display[*y][j - 1];
                        }
                        display[*y][0] = tmp;
                    }
                }
            }
        }
        for l in display.iter() {
            for c in l.iter() {
                print!("{}", if *c { '#' } else { ' ' });
            }
            println!();
        }
        0
    }
}
