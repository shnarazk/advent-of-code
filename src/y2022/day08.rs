//! <https://adventofcode.com/2022/day/8>
use {
    crate::framework::{aoc, AdventOfCode, ParseError},
    std::collections::HashMap,
};

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Puzzle {
    line: Vec<Vec<usize>>,
    map: HashMap<(usize, usize), usize>,
}

#[aoc(2022, 8)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.line.push(
            block
                .chars()
                .map(|c| c as usize - '0' as usize)
                .collect::<Vec<_>>(),
        );
        Ok(())
    }
    fn end_of_data(&mut self) {
        for (y, l) in self.line.iter().enumerate() {
            for (x, h) in l.iter().enumerate() {
                self.map.insert((y, x), *h);
            }
        }
        // dbg!(&self.map);
    }
    fn part1(&mut self) -> Self::Output1 {
        let height = self.line.len();
        let width = self.line[0].len();
        self.map
            .iter()
            .filter(|((y, x), h)| {
                (0..*y).all(|yy| self.map.get(&(yy, *x)).unwrap() < h)
                    || (*y + 1..height).all(|yy| self.map.get(&(yy, *x)).unwrap() < h)
                    || (0..*x).all(|xx| self.map.get(&(*y, xx)).unwrap() < h)
                    || (*x + 1..width).all(|xx| self.map.get(&(*y, xx)).unwrap() < h)
            })
            .count()
    }
    fn part2(&mut self) -> Self::Output2 {
        self.map
            .iter()
            .map(|((y, x), _)| self.scenic_score(*y, *x))
            .max()
            .unwrap()
    }
}

impl Puzzle {
    fn scenic_score(&self, y: usize, x: usize) -> usize {
        let h = *self.map.get(&(y, x)).unwrap();
        let height = self.line.len();
        let width = self.line[0].len();
        let mut point = 1;
        let mut tmp = 0;
        for yy in (0..y).rev() {
            tmp += 1;
            if h <= *self.map.get(&(yy, x)).unwrap() {
                break;
            }
        }
        point *= tmp;
        tmp = 0;
        for yy in y + 1..height {
            tmp += 1;
            if h <= *self.map.get(&(yy, x)).unwrap() {
                break;
            }
        }
        point *= tmp;
        tmp = 0;
        for xx in (0..x).rev() {
            tmp += 1;
            if h <= *self.map.get(&(y, xx)).unwrap() {
                break;
            }
        }
        point *= tmp;
        tmp = 0;
        for xx in x + 1..width {
            tmp += 1;
            if h <= *self.map.get(&(y, xx)).unwrap() {
                break;
            }
        }
        point *= tmp;
        point
    }
}
