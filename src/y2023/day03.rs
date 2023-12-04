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
            if c.is_ascii_digit() {
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
        self.number
            .iter()
            .map(|((y, x1, x2), val)| {
                self.symbol
                    .iter()
                    .any(|(sy, sx, _)| y.abs_diff(*sy) <= 1 && *x1 <= *sx + 1 && *sx <= *x2 + 1)
                    as usize
                    * val
            })
            .sum::<usize>()
    }
    fn part2(&mut self) -> Self::Output2 {
        self.symbol
            .iter()
            .filter(|d| d.2 == '*')
            .map(|(y, x, _)| -> usize {
                let s = self
                    .number
                    .iter()
                    .filter(|((ny, x1, x2), _)| {
                        y.abs_diff(*ny) <= 1 && *x1 <= *x + 1 && *x <= *x2 + 1
                    })
                    .map(|(_, val)| *val)
                    .collect::<Vec<_>>();
                (s.len() == 2) as usize * s.iter().product::<usize>()
            })
            .sum::<usize>()
    }
}
