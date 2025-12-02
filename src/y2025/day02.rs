//! <https://adventofcode.com/2025/day/2>
use crate::framework::{AdventOfCode, ParseError, aoc};

#[derive(Clone, Debug, Default)]
pub struct Puzzle {
    line: Vec<(usize, usize)>,
}

mod parser {
    use {
        crate::parser::parse_usize,
        winnow::{
            ModalResult, Parser,
            combinator::{separated, seq},
        },
    };
    fn parse_line(s: &mut &str) -> ModalResult<(usize, usize)> {
        seq!(parse_usize, "-", parse_usize)
            .parse_next(s)
            .map(|(a, _, b)| (a, b))
    }
    pub fn parse(s: &mut &str) -> ModalResult<Vec<(usize, usize)>> {
        separated(1.., parse_line, ",").parse_next(s)
    }
}

#[aoc(2025, 2)]
impl AdventOfCode for Puzzle {
    fn prepare(&mut self, mut input: &str) -> Result<(), ParseError> {
        self.line = parser::parse(&mut input)?;
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut found = 0;
        for (s, e) in self.line.iter() {
            for n in *s..=*e {
                if satisfies(n) {
                    found += n;
                };
            }
        }
        found
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut found = 0;
        for (s, e) in self.line.iter() {
            for n in *s..=*e {
                if satisfies2(n) {
                    found += n;
                };
            }
        }
        found
    }
}

fn satisfies(n: usize) -> bool {
    let v = vectorize(n);
    if v.len() % 2 == 1 {
        return false;
    }
    let offset = v.len() / 2;
    v[..offset]
        .iter()
        .enumerate()
        .all(|(i, n)| *n == v[offset + i])
}

fn satisfies2(n: usize) -> bool {
    let v = vectorize(n);
    'next: for m in 2..=v.len().max(2) {
        if v.len() % m == 0 {
            let l = v.len() / m;
            for (i, d) in v.iter().take(l).enumerate() {
                if !(1..m).all(|r| v[i + r * l] == *d) {
                    continue 'next;
                }
            }
            return true;
        }
    }
    false
}

fn vectorize(mut n: usize) -> Vec<usize> {
    let mut v: Vec<usize> = Vec::new();
    while n > 0 {
        v.push(n % 10);
        n /= 10;
    }
    v.reverse();
    v
}
