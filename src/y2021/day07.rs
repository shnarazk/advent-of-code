//! <https://adventofcode.com/2021/day/7>
use crate::{
    framework::{AdventOfCode, ParseError, aoc},
    parser,
};

#[derive(Clone, Debug, Default)]
pub struct Puzzle {
    config: Vec<usize>,
}

#[aoc(2021, 7)]
impl AdventOfCode for Puzzle {
    fn prepare(&mut self, input: &str) -> Result<(), ParseError> {
        self.config = parser::to_usizes(input, &[','])?;
        Ok(())
    }
    fn part1(&mut self) -> usize {
        let vec = &self.config;
        let len: usize = *vec.iter().max().unwrap();
        let mut fmin: usize = vec.iter().sum::<usize>().pow(2);
        for pos in 0..=len {
            fmin = fmin.min(
                vec.iter()
                    .map(|i| (*i as isize - pos as isize).unsigned_abs())
                    .sum(),
            );
        }
        fmin
    }
    fn part2(&mut self) -> usize {
        let vec = &self.config;
        let len: usize = *vec.iter().max().unwrap();
        let mut fuel_table: Vec<Option<usize>> = Vec::new();
        fuel_table.resize(len + 1, None);
        fuel_table[0] = Some(0);
        fn get(table: &mut Vec<Option<usize>>, n: usize) -> usize {
            if let Some(k) = table[n] {
                k
            } else {
                let v = n + get(table, n - 1);
                table[n] = Some(v);
                v
            }
        }
        let mut fmin: usize = vec.iter().sum::<usize>() * vec.len();
        for pos in 0..=len {
            fmin = fmin.min(
                vec.iter()
                    .map(|i| get(&mut fuel_table, (*i as isize - pos as isize).unsigned_abs()))
                    .sum(),
            );
        }
        fmin
    }
}
