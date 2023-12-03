//! <https://adventofcode.com/2023/day/3>
use {
    crate::framework::{aoc, AdventOfCode, ParseError},
    std::collections::HashMap,
};

#[derive(Debug, Default)]
pub struct Puzzle {
    line: usize,
    number: HashMap<(usize, usize, usize), usize>,
    symbol: Vec<(usize, usize, char)>,
}

#[aoc(2023, 3)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        let cs = block.chars().collect::<Vec<_>>();
        let mut acc: Option<usize> = None;
        let mut pos_start = 0;
        for (j, c) in cs.iter().enumerate() {
            if c.is_digit(10) {
                let n = (*c as u8 - b'0') as usize;
                if let Some(a) = acc {
                    acc = Some(a * 10 + n);
                } else {
                    acc = Some(n);
                    pos_start = j;
                }
            } else {
                if *c != '.' {
                    self.symbol.push((self.line, j, *c));
                }
                if let Some(n) = acc {
                    // dbg!((self.line, pos_start, j), n);
                    self.number.insert((self.line, pos_start, j - 1), n);
                    acc = None;
                }
            }
        }
        if let Some(n) = acc {
            self.number.insert((self.line, pos_start, cs.len()), n);
        }
        self.line += 1;
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut sum = 0;
        for ((y, x1, x2), val) in self.number.iter() {
            if self
                .symbol
                .iter()
                .any(|(sy, sx, _)| y.abs_diff(*sy) <= 1 && *x1 <= *sx + 1 && *sx <= *x2 + 1)
            {
                sum += val;
            }
        }
        sum
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut sum = 0;
        for (y, x, _) in self.symbol.iter().filter(|d| d.2 == '*') {
            let mut count = 0;
            let mut s = 1;
            for ((ny, x1, x2), val) in self.number.iter() {
                if y.abs_diff(*ny) <= 1 && *x1 <= *x + 1 && *x <= *x2 + 1 {
                    count += 1;
                    s *= val;
                }
            }
            if count == 2 {
                sum += s;
            }
        }
        sum
    }
}
