//! <https://adventofcode.com/2023/day/9>
use crate::{
    framework::{AdventOfCode, ParseError, aoc},
    parser,
};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Vec<isize>>,
}

#[aoc(2023, 9)]
impl AdventOfCode for Puzzle {
    fn prepare(&mut self, input: &str) -> Result<(), ParseError> {
        self.line = input
            .lines()
            .map(|l| parser::to_isizes(l, &[' ']).unwrap())
            .collect();
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        self.line.iter_mut().map(|v| extrapolate(v)).sum::<isize>() as usize
    }
    fn part2(&mut self) -> Self::Output2 {
        self.line
            .iter_mut()
            .map(|v| extrapolate_backword(v))
            .sum::<isize>() as usize
    }
}

fn extrapolate(vec: &mut [isize]) -> isize {
    let mut level = 0;
    let len = vec.len();
    while !vec.iter().skip(level).all(|n| *n == 0) {
        level += 1;
        let l = vec[len - 1];
        for i in (level..len).rev() {
            vec[i] -= vec[i - 1];
        }
        if level == 1 {
            vec[0] = 0;
        }
        vec[0] += l;
    }
    vec[0]
}

fn extrapolate_backword(vec: &mut [isize]) -> isize {
    let mut level = 0;
    let len = vec.len();
    while !vec.iter().skip(level).all(|n| *n == 0) {
        level += 1;
        for i in (level..len).rev() {
            vec[i] -= vec[i - 1];
        }
    }
    for i in (1..level).rev() {
        vec[i - 1] -= vec[i];
    }
    vec[0]
}
