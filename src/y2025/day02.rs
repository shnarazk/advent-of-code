//! <https://adventofcode.com/2025/day/2>
use {
    crate::framework::{AdventOfCode, ParseError, aoc},
    rayon::prelude::*,
};

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
            found += (*s..*e)
                .into_par_iter()
                .map(|n| {
                    check_occurences(n)
                        .and_then(|_| satisfies(n).then(|| n))
                        .unwrap_or(0)
                })
                .sum::<usize>();
        }
        found
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut found = 0;
        for (s, e) in self.line.iter() {
            found += (*s..*e)
                .into_par_iter()
                .map(|n| {
                    check_occurences(n)
                        .and_then(|k| satisfies2(n, k).then(|| n))
                        .unwrap_or(0)
                })
                .sum::<usize>();
        }
        found
    }
}

fn check_occurences(mut n: usize) -> Option<u8> {
    let mut occs = [0_u8; 10];
    while n > 0 {
        occs[n % 10] += 1;
        n /= 10;
    }
    let k = *occs.iter().filter(|k| **k > 0).min().unwrap();
    (k > 1 && occs.iter().all(|o| *o % k == 0)).then_some(k)
}

fn satisfies(n: usize) -> bool {
    let v = vectorize(n);
    let offset = v.len() / 2;
    v[..offset] == v[offset..]
}

fn satisfies2(n: usize, k: u8) -> bool {
    let v = vectorize(n);
    for m in [2, 3, 5, 7, 11, 13, 17] {
        if k % m == 0 {
            let l = v.len() / m as usize;
            if (1..m as usize).all(|r| v[..l] == v[r * l..(r + 1) * l]) {
                return true;
            }
        }
    }
    false
}

fn vectorize(mut n: usize) -> Vec<u8> {
    let mut v: Vec<u8> = Vec::new();
    while n > 0 {
        v.push((n % 10) as u8);
        n /= 10;
    }
    v.reverse();
    v
}
