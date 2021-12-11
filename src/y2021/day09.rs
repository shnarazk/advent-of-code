use crate::{
    framework::{aoc_at, AdventOfCode, Maybe},
    geometric::neighbors,
};

#[derive(Debug, Default, PartialEq)]
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
            for jj in neighbors(j, h + 1) {
                for ii in neighbors(i, w + 1) {
                    if let (Some(y), Some(x)) = (jj, ii) {
                        if (y == j || x == i)
                            && !(y == j && x == i)
                            && here < self.line[y][x]
                            && !to_check.contains(&(y, x))
                            && !checked.contains(&(y, x))
                        {
                            to_check.push((y, x));
                        }
                    }
                }
            }
        }
        checked.len()
    }
}

#[aoc_at(2021, 9)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Maybe<()> {
        self.line.push(
            block
                .trim()
                .chars()
                .map(|c| c.to_digit(10).unwrap() as usize)
                .collect::<Vec<usize>>(),
        );
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
                for jj in neighbors(j, height) {
                    for ii in neighbors(i, width) {
                        if let (Some(jj), Some(ii)) = (jj, ii) {
                            if (jj == j || ii == i)
                                && !(jj == j && ii == i)
                                && self.line[jj][ii] <= here
                            {
                                continue 'next;
                            }
                        }
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
                if (if j != 0 {
                    here < self.line[j - 1][i]
                } else {
                    true
                } && if j + 1 != height {
                    here < self.line[j + 1][i]
                } else {
                    true
                } && if i != 0 {
                    here < self.line[j][i - 1]
                } else {
                    true
                } && if i + 1 != width {
                    here < self.line[j][i + 1]
                } else {
                    true
                }) {
                    dbg!(self.basin_size(height - 1, width - 1, j, i));
                    sizes.push(self.basin_size(height - 1, width - 1, j, i));
                }
            }
        }
        sizes.sort_unstable();
        sizes.reverse();
        sizes[0] * sizes[1] * sizes[2]
    }
}
