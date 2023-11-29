//! <https://adventofcode.com/2021/day/13>
use {
    crate::framework::{aoc, AdventOfCode, ParseError},
    regex::Regex,
};

fn folding_x(vec: &[Vec<bool>], pos: usize) -> Vec<Vec<bool>> {
    let mut result: Vec<Vec<bool>> = Vec::new();
    for v in vec.iter() {
        result.push(
            v.iter()
                .enumerate()
                .take(pos)
                .map(|(i, b)| {
                    if let Some(c) = v.get(2 * pos - i) {
                        *b || *c
                    } else {
                        *b
                    }
                })
                .collect::<Vec<bool>>(),
        );
    }
    result
}

fn folding_y(vec: &[Vec<bool>], pos: usize) -> Vec<Vec<bool>> {
    let mut result: Vec<Vec<bool>> = Vec::new();
    for i in 0..pos {
        if let Some(w) = vec.get(pos - i + pos) {
            result.push(
                vec[i]
                    .iter()
                    .enumerate()
                    .map(|(i, b)| *b || w[i])
                    .collect::<Vec<bool>>(),
            );
        } else {
            result.push(vec[i].clone());
        }
    }
    result
}

fn print_grid(vec: &[Vec<bool>]) {
    for v in vec.iter() {
        for b in v.iter() {
            print!("{}", if *b { '#' } else { '.' });
        }
        println!();
    }
}

#[derive(Debug, Default)]
pub struct Puzzle {
    line: Vec<(usize, usize)>,
    grid: Vec<Vec<bool>>,
    folding: Vec<(bool, usize)>,
}

#[aoc(2021, 13)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        let num_pair: Regex = Regex::new(r"^([0-9]+),([0-9]+)$").expect("wrong");
        let props: Regex = Regex::new(r"^fold along (x|y)=([0-9]+)$").expect("wrong");
        if let Some(segment) = num_pair.captures(block) {
            self.line
                .push((segment[2].parse::<usize>()?, segment[1].parse::<usize>()?));
        } else if let Some(segment) = props.captures(block) {
            self.folding
                .push((&segment[1] == "x", segment[2].parse::<usize>()?));
        }
        Ok(())
    }
    fn wrap_up(&mut self) {
        let height = self.line.iter().map(|(y, _)| y).max().unwrap() + 1;
        let width = self.line.iter().map(|(_, x)| x).max().unwrap() + 1;
        self.grid = Vec::new();
        self.grid.resize(height, Vec::new());
        for v in self.grid.iter_mut() {
            v.resize(width, false);
        }
        for (j, i) in self.line.iter() {
            self.grid[*j][*i] = true;
        }
        print_grid(&self.grid);
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut r = self.grid.clone();
        for (axis_is_x, pos) in self.folding.iter().take(1) {
            if *axis_is_x {
                r = folding_x(&r, *pos);
                // print_grid(&r);
            } else {
                r = folding_y(&r, *pos);
                // print_grid(&r);
            }
        }
        r.iter().map(|v| v.iter().filter(|b| **b).count()).sum()
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut r = self.grid.clone();
        for (axis_is_x, pos) in self.folding.iter() {
            if *axis_is_x {
                r = folding_x(&r, *pos);
            } else {
                r = folding_y(&r, *pos);
            }
        }
        print_grid(&r);
        0
    }
}
