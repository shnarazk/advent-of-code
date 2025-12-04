//! <https://adventofcode.com/2025/day/3>
use {
    crate::framework::{AdventOfCode, ParseError, aoc},
    rayon::prelude::*,
};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Vec<u8>>,
}

mod parser {
    use {
        crate::parser::parse_dec,
        winnow::{
            ModalResult, Parser,
            ascii::newline,
            combinator::{repeat, separated},
        },
    };

    fn parse_line(s: &mut &str) -> ModalResult<Vec<u8>> {
        repeat(1.., parse_dec.map(|x| x as u8)).parse_next(s)
    }

    pub fn parse(s: &mut &str) -> ModalResult<Vec<Vec<u8>>> {
        separated(1.., parse_line, newline).parse_next(s)
    }
}

#[aoc(2025, 3)]
impl AdventOfCode for Puzzle {
    fn prepare(&mut self, mut input: &str) -> Result<(), ParseError> {
        self.line = parser::parse(&mut input)?;
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        self.line
            .par_iter()
            .map(|line| {
                let mut a = [line[line.len() - 2], line[line.len() - 1]];
                for n in line.iter().rev().skip(2) {
                    if *n >= a[0] {
                        a[1] = a[1].max(a[0]);
                        a[0] = *n;
                    }
                }
                (a[0] * 10 + a[1]) as usize
            })
            .sum::<usize>()
    }
    fn part2(&mut self) -> Self::Output2 {
        self.line
            .par_iter()
            .map(|line| {
                let mut a = line[line.len() - 12..].to_vec();
                for n in line.iter().rev().skip(12) {
                    let mut x = *n;
                    for r in a.iter_mut() {
                        if x >= *r {
                            std::mem::swap(&mut x, r);
                        } else {
                            break;
                        }
                    }
                }
                a.iter().fold(0, |acc, &x| acc * 10 + x as usize)
            })
            .sum::<usize>()
    }
}
