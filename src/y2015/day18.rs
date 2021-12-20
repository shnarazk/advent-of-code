//! <https://adventofcode.com/2015/day/18>
use crate::{
    framework::{aoc, AdventOfCode, ParseError},
    geometric, line_parser,
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Vec<char>>,
}

#[aoc(2015, 18)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.line.push(line_parser::to_chars(block)?);
        Ok(())
    }
    fn after_insert(&mut self) {
        // dbg!(&self.line);
    }
    fn part1(&mut self) -> Self::Output1 {
        let count = 100;
        let mut grid: Vec<Vec<char>> = self.line.clone();
        let height = grid.len();
        let width = grid[0].len();
        for _ in 0..count {
            let mut next = grid.clone();
            for (j, v) in grid.iter().enumerate() {
                for (i, _) in v.iter().enumerate() {
                    let n = geometric::neighbors8(j, i, height, width)
                        .iter()
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
            //     println!("{:?}", v.iter().map(|c| format!("{}", c)).collect::<Vec<_>>().join(""));
            // }
        }
        for v in grid.iter() {
            println!(
                "{:?}",
                v.iter()
                    .map(|c| format!("{}", c))
                    .collect::<Vec<_>>()
                    .join("")
            );
        }
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
                for (i, _) in v.iter().enumerate() {
                    let n = geometric::neighbors8(j, i, height, width)
                        .iter()
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
            //     println!("{:?}", v.iter().map(|c| format!("{}", c)).collect::<Vec<_>>().join(""));
            // }
        }
        for v in grid.iter() {
            println!(
                "{:?}",
                v.iter()
                    .map(|c| format!("{}", c))
                    .collect::<Vec<_>>()
                    .join("")
            );
        }
        grid.iter()
            .map(|v| v.iter().filter(|l| **l == '#').count())
            .sum()
    }
}

#[cfg(feature = "y2015")]
#[cfg(test)]
mod test {
    use {
        super::*,
        crate::framework::{Answer, Description},
    };

    // #[test]
    // fn test_part1() {
    //     assert_eq!(
    //         Puzzle::solve(Description::TestData("".to_string()), 1),
    //         Answer::Part1(0)
    //     );
    // }
}
