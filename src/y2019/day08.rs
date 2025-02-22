//! <https://adventofcode.com/2019/day/8>
use crate::framework::{AdventOfCode, ParseError, aoc_at};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<u8>,
}

#[aoc_at(2019, 8)]
impl AdventOfCode for Puzzle {
    type Output1 = usize;
    type Output2 = usize;
    fn parse(&mut self, input: &str) -> Result<(), ParseError> {
        self.line = input
            .trim()
            .chars()
            .map(|c| c as u8 - b'0')
            .collect::<Vec<u8>>();
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        let width = 25;
        let height = 6;
        let delta = width * height;
        let n_layers = self.line.len() / delta;
        let mut target: usize = 0;
        let mut min_zeros: usize = delta;
        for start in (0..n_layers).map(|i| i * delta) {
            let n_zeros = (start..start + delta)
                .filter(|i| self.line[*i] == 0)
                .count();
            if n_zeros < min_zeros {
                min_zeros = n_zeros;
                target = start;
            }
        }
        (target..target + delta)
            .filter(|i| self.line[*i] == 1)
            .count()
            * (target..target + delta)
                .filter(|i| self.line[*i] == 2)
                .count()
    }
    fn part2(&mut self) -> Self::Output2 {
        let width = 25;
        let height = 6;
        let delta = width * height;
        let n_layers = self.line.len() / delta;
        for j in 0..height {
            for i in 0..width {
                for q in (0..n_layers).map(|l| l * delta + j * width + i) {
                    match self.line[q] {
                        0 => {
                            print!(" ");
                            break;
                        }
                        1 => {
                            print!("*");
                            break;
                        }
                        _ => (),
                    }
                }
            }
            println!();
        }
        0
    }
}
