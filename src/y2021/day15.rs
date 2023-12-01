//! <https://adventofcode.com/2021/day/15>
use crate::{
    framework::{aoc, AdventOfCode, ParseError},
    geometric, line_parser,
};

#[derive(Debug, Default)]
pub struct Puzzle {
    line: Vec<Vec<usize>>,
}

impl Puzzle {
    fn build_up(&mut self) -> Vec<Vec<usize>> {
        let height = self.line.len();
        let width = self.line[0].len();
        let mut dist = self.line.clone();
        for v in dist.iter_mut() {
            for i in v.iter_mut() {
                *i = usize::MAX;
            }
        }
        dist[0][0] = 0;
        dist[0][1] = self.line[0][1];
        dist[1][0] = self.line[1][0];
        let mut cands: Vec<(usize, usize)> = vec![(0, 1), (1, 0)];
        while let Some(n) = cands.iter().min_by_key(|(j, i)| dist[*j][*i]) {
            let node = (n.0, n.1);
            cands.retain(|p| *p != node);
            for neighbor in geometric::neighbors4(node.0, node.1, height, width) {
                let new_dist = dist[node.0][node.1] + self.line[neighbor.0][neighbor.1];
                if new_dist < dist[neighbor.0][neighbor.1] {
                    dist[neighbor.0][neighbor.1] = new_dist;
                    if !cands.contains(&neighbor) {
                        cands.push(neighbor);
                    }
                }
            }
        }
        dist
    }
    fn extend5(&mut self) {
        let height = self.line.len();
        let width = self.line[0].len();
        let mut grid: Vec<Vec<usize>> = Vec::new();
        for _ in 0..height * 5 {
            let mut v: Vec<usize> = Vec::new();
            v.resize(width * 5, 0);
            grid.push(v);
        }
        for dj in 0..5 {
            for di in 0..5 {
                for j in 0..height {
                    for i in 0..width {
                        grid[height * dj + j][width * di + i] =
                            (self.line[j][i] + dj + di - 1) % 9 + 1;
                    }
                }
            }
        }
        std::mem::swap(&mut self.line, &mut grid);
    }
}

#[aoc(2021, 15)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.line.push(line_parser::to_digits(block)?);
        Ok(())
    }
    fn end_of_data(&mut self) {
        // for l in self.line.iter() {
        //     println!{"{:?}", &l};
        // }
    }
    fn part1(&mut self) -> Self::Output1 {
        let height = self.line.len();
        let width = self.line[0].len();
        let dist = self.build_up();
        dist[height - 1][width - 1]
    }
    fn part2(&mut self) -> Self::Output2 {
        self.extend5();
        for l in self.line.iter() {
            println!(
                "{}",
                l.iter()
                    .map(|n| (*n as u8 + b'0') as char)
                    .collect::<String>()
            );
        }
        self.part1()
    }
}
