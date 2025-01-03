//! <https://adventofcode.com/2015/day/25>
use crate::framework::{aoc_at, AdventOfCode, ParseError};

fn at(j: usize, i: usize) -> usize {
    (1..j + i - 1).sum::<usize>() + i
}

fn code(j: usize, i: usize) -> usize {
    let mut n = 20151125;
    for _ in 1..at(j, i) {
        n *= 252533;
        n %= 33554393;
    }
    n
}

#[derive(Clone, Debug, Default)]
pub struct Puzzle {}

#[aoc_at(2015, 25)]
impl AdventOfCode for Puzzle {
    type Output1 = usize;
    type Output2 = String;
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, _block: &str) -> Result<(), ParseError> {
        Ok(())
    }
    fn end_of_data(&mut self) {
        // for j in 1..=6 {
        //     for i in 1..=6 {
        //         print!("{:>4}", at(j, i));
        //     }
        //     println!();
        // }
        // println!();
    }
    fn part1(&mut self) -> Self::Output1 {
        // Enter the code at row 2981, column 3075.
        // for j in 1..=6 {
        //     for i in 1..=6 {
        //         print!("{:>10}", code(j, i));
        //     }
        //     println!();
        // }
        code(2981, 3075)
    }
    fn part2(&mut self) -> Self::Output2 {
        "That's it.".to_string()
    }
}
