//! <https://adventofcode.com/2021/day/9>
use crate::{
    framework::{AdventOfCode, ParseError, aoc},
    geometric,
};

#[derive(Clone, Debug, Default)]
pub struct Puzzle {
    line: Vec<Vec<usize>>,
}

impl Puzzle {
    fn basin_size(&self, h: usize, w: usize, j: usize, i: usize) -> usize {
        let mut to_check: Vec<(usize, usize)> = vec![(j, i)];
        let mut checked: Vec<(usize, usize)> = Vec::new();
        while let Some(pos @ (j, i)) = to_check.pop() {
            let here = self.line[j][i];
            if here == 9 {
                continue;
            }
            checked.push(pos);
            for (jj, ii) in geometric::neighbors4(j, i, h + 1, w + 1) {
                if here < self.line[jj][ii]
                    && !to_check.contains(&(jj, ii))
                    && !checked.contains(&(jj, ii))
                {
                    to_check.push((jj, ii));
                }
            }
        }
        checked.len()
    }
}

#[aoc(2021, 9)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, input: &str) -> Result<(), ParseError> {
        self.line = input
            .lines()
            .map(|line| {
                line.trim()
                    .chars()
                    .map(|c| c.to_digit(10).unwrap() as usize)
                    .collect::<Vec<usize>>()
            })
            .collect::<Vec<_>>();
        Ok(())
    }
    fn part1(&mut self) -> usize {
        // dbg!(&self.line);
        let height = self.line.len();
        let width = self.line[0].len();
        let mut risks = 0;
        for j in 0..height {
            'next: for i in 0..width {
                let here = self.line[j][i];
                for (jj, ii) in geometric::neighbors4(j, i, height, width) {
                    if self.line[jj][ii] <= here {
                        continue 'next;
                    }
                }
                risks += self.line[j][i] + 1;
            }
        }
        risks
    }
    fn part2(&mut self) -> usize {
        let height = self.line.len();
        let width = self.line[0].len();
        let mut sizes = Vec::new();
        for j in 0..height {
            for i in 0..width {
                let here = self.line[j][i];
                if geometric::neighbors4(j, i, height, width)
                    .iter()
                    .all(|(y, x)| here < self.line[*y][*x])
                {
                    // dbg!(self.basin_size(height - 1, width - 1, j, i));
                    sizes.push(self.basin_size(height - 1, width - 1, j, i));
                }
            }
        }
        sizes.sort_unstable();
        sizes.reverse();
        sizes[0] * sizes[1] * sizes[2]
    }
}
