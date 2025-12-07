//! <https://adventofcode.com/2015/day/18>
use crate::{
    framework::{AdventOfCode, ParseError, aoc},
    geometric::NeighborIter,
};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Vec<char>>,
}

#[aoc(2015, 18)]
impl AdventOfCode for Puzzle {
    fn prepare(&mut self, s: &str) -> Result<(), ParseError> {
        self.line = s.lines().map(|l| l.chars().collect()).collect();
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        let count = 100;
        let mut grid: Vec<Vec<char>> = self.line.clone();
        let height = grid.len();
        let width = grid[0].len();
        for _ in 0..count {
            let mut next = grid.clone();
            for (j, v) in grid.iter().enumerate() {
                for i in 0..v.len() {
                    let n = (j, i)
                        .iter8(&(height, width))
                        .filter(|(jj, ii)| grid[*jj][*ii] == '#')
                        .count();
                    match (grid[j][i], n) {
                        ('#', 2) | ('#', 3) => {
                            next[j][i] = '#';
                        }
                        ('#', _) => {
                            next[j][i] = '.';
                        }
                        ('.', 3) => {
                            next[j][i] = '#';
                        }
                        ('.', _) => {
                            next[j][i] = '.';
                        }
                        _ => unreachable!(),
                    }
                }
            }
            std::mem::swap(&mut grid, &mut next);
            // println!("");
            // for v in grid.iter() {
            //     println!("{:?}", v.iter().collect::<String>());
            // }
        }
        // for v in grid.iter() {
        //     println!("{}", v.iter().collect::<String>());
        // }
        grid.iter()
            .map(|v| v.iter().filter(|l| **l == '#').count())
            .sum()
    }
    fn part2(&mut self) -> Self::Output2 {
        let count = 100;
        let mut grid: Vec<Vec<char>> = self.line.clone();
        let height = grid.len();
        let width = grid[0].len();
        grid[0][0] = '#';
        grid[0][width - 1] = '#';
        grid[height - 1][0] = '#';
        grid[height - 1][width - 1] = '#';
        for _ in 0..count {
            let mut next = grid.clone();
            for (j, v) in grid.iter().enumerate() {
                for i in 0..v.len() {
                    let n = (j, i)
                        .iter8(&(height, width))
                        .filter(|(jj, ii)| grid[*jj][*ii] == '#')
                        .count();
                    match (grid[j][i], n) {
                        ('#', 2) | ('#', 3) => {
                            next[j][i] = '#';
                        }
                        ('#', _) => {
                            next[j][i] = '.';
                        }
                        ('.', 3) => {
                            next[j][i] = '#';
                        }
                        ('.', _) => {
                            next[j][i] = '.';
                        }
                        _ => unreachable!(),
                    }
                }
            }
            next[0][0] = '#';
            next[0][width - 1] = '#';
            next[height - 1][0] = '#';
            next[height - 1][width - 1] = '#';
            std::mem::swap(&mut grid, &mut next);
            // println!("");
            // for v in grid.iter() {
            //     println!("{}", v.iter().collect::<String>());
            // }
        }
        // for v in grid.iter() {
        //     println!("{}", v.iter().collect::<String>());
        // }
        grid.iter()
            .map(|v| v.iter().filter(|l| **l == '#').count())
            .sum()
    }
}
