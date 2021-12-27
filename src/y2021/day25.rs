//! <https://adventofcode.com/2021/day/25>
use crate::{
    framework::{aoc_at, AdventOfCode, ParseError},
    line_parser,
};

#[derive(Debug, Default)]
pub struct Puzzle {
    line: Vec<Vec<char>>,
}

#[aoc_at(2021, 25)]
impl AdventOfCode for Puzzle {
    type Output1 = usize;
    type Output2 = String;
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.line.push(line_parser::to_chars(block)?);
        Ok(())
    }
    fn after_insert(&mut self) {
        // dbg!(&self.line);
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut grid = Grid {
            height: self.line.len(),
            width: self.line[0].len(),
            loc: self.line.clone(),
        };
        grid.show();
        for i in 1.. {
            let new_grid = grid.shift_right().shift_down();
            if grid == new_grid {
                grid.show();
                return i;
            }
            grid = new_grid;
        }
        unreachable!()
    }
    fn part2(&mut self) -> Self::Output2 {
        "That's it!".to_string()
    }
}

#[derive(Debug, Default, Eq, PartialEq)]
struct Grid {
    height: usize,
    width: usize,
    loc: Vec<Vec<char>>,
}

impl Grid {
    fn show(&self) {
        for v in self.loc.iter() {
            for c in v.iter() {
                print!("{}", c);
            }
            println!();
        }
        println!();
    }
    fn below(&self, n: usize) -> usize {
        (n + 1) % self.height
    }
    fn right(&self, n: usize) -> usize {
        (n + 1) % self.width
    }
    fn shift_right(&self) -> Self {
        let mut grid = self.loc.clone();
        for (j, v) in self.loc.iter().enumerate() {
            for (i, p) in v.iter().enumerate() {
                let t = self.right(i);
                if *p == '>' && v[t] == '.' {
                    grid[j][i] = '.';
                    grid[j][t] = '>';
                }
            }
        }
        Grid {
            height: self.height,
            width: self.width,
            loc: grid,
        }
    }
    fn shift_down(&self) -> Self {
        let mut grid = self.loc.clone();
        for (j, v) in self.loc.iter().enumerate() {
            let t = self.below(j);
            for (i, p) in v.iter().enumerate() {
                if *p == 'v' && self.loc[t][i] == '.' {
                    grid[j][i] = '.';
                    grid[t][i] = 'v';
                }
            }
        }
        Grid {
            height: self.height,
            width: self.width,
            loc: grid,
        }
    }
}
