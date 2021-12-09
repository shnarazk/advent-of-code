use crate::{AdventOfCode, Description, ParseError, TryParse};

#[derive(Debug, PartialEq)]
struct DataSegment(Vec<usize>);

impl TryParse for DataSegment {
    fn parse(s: &str) -> Result<Self, ParseError> {
        Ok(DataSegment(
            s.trim()
                .chars()
                .map(|c| c.to_digit(10).unwrap() as usize)
                .collect::<Vec<usize>>(),
        ))
    }
}

fn basin_size(grid: &[Vec<usize>], h: usize, w: usize, j: usize, i: usize) -> usize {
    let mut to_check: Vec<(usize, usize)> = vec![(j,i)];
    let mut checked: Vec<(usize, usize)> = Vec::new();
    while let Some(pos@(j, i)) = to_check.pop() {
        let here = grid[j][i];
        if here == 9 {
            continue;
        }
        checked.push(pos);
        if j != 0 {
            let new = (j - 1, i);
            if here < grid[new.0][new.1] && !to_check.contains(&new) && !checked.contains(&new) {
                to_check.push(new);
            }
        }
        if j != h {
            let new = (j + 1, i);
            if here < grid[new.0][new.1] && !to_check.contains(&new) && !checked.contains(&new) {
                to_check.push(new);
            }
        }
        if i != 0 {
            let new = (j, i - 1);
            if here < grid[new.0][new.1] && !to_check.contains(&new) && !checked.contains(&new) {
                to_check.push(new);
            }
        }
        if i != w {
            let new = (j, i + 1);
            if here < grid[new.0][new.1] && !to_check.contains(&new) && !checked.contains(&new) {
                to_check.push(new);
            }
        }
    }
    checked.len()
}

#[derive(Debug, PartialEq)]
struct Puzzle {
    line: Vec<Vec<usize>>,
}

impl AdventOfCode for Puzzle {
    type Segment = DataSegment;
    type Output1 = usize;
    type Output2 = usize;
    const YEAR: usize = 2021;
    const DAY: usize = 9;
    const DELIMITER: &'static str = "\n";
    fn default() -> Self {
        Self { line: Vec::new() }
    }
    fn insert(&mut self, object: Self::Segment) {
        self.line.push(object.0);
    }
    fn part1(&mut self) -> usize {
        // dbg!(&self.line);
        let height = self.line.len();
        let width = self.line[0].len();
        let mut risks = 0;
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
                    risks += self.line[j][i] + 1;
                }
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
                    dbg!(basin_size(&self.line, height - 1, width - 1, j, i));
                    sizes.push(basin_size(&self.line, height - 1, width - 1, j, i));
                }
            }
        }
        sizes.sort_unstable();
        sizes.reverse();
        sizes[0] * sizes[1] * sizes[2]
    }
}

pub fn go(part: usize, desc: Description) {
    dbg!(Puzzle::solve(&desc, part));
}
