//! <https://adventofcode.com/2016/day/15>
use crate::framework::{AdventOfCode, ParseError, aoc};

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Puzzle {
    line: Vec<(usize, usize)>,
}

mod parser {
    use {
        crate::parser::parse_usize,
        winnow::{
            ModalResult, Parser,
            ascii::newline,
            combinator::{separated, seq},
        },
    };

    fn parse_line(s: &mut &str) -> ModalResult<(usize, usize)> {
        seq!(_: "Disc #", _: parse_usize, _: " has ", parse_usize, _: " positions; at time=", _: parse_usize, _: ", it is at position ", parse_usize, _: ".").parse_next(s)
    }

    pub fn parse(s: &mut &str) -> ModalResult<Vec<(usize, usize)>> {
        separated(1.., parse_line, newline).parse_next(s)
    }
}

#[aoc(2016, 15)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, mut input: &str) -> Result<(), ParseError> {
        self.line = parser::parse(&mut input)?;
        Self::parsed()
    }
    fn part1(&mut self) -> usize {
        // self.line.clear();
        // self.line.push((5, 4));
        // self.line.push((2, 0));
        // self.line.push((7, 2));
        let mut x = self.line[0];
        for (i, tuple) in self.line.iter().enumerate() {
            let mut m = (tuple.0 + tuple.1 + ((i + 1) % tuple.0)) % tuple.0;
            m = tuple.0 - m;
            // println!("周期{}で{}start", tuple.0, m);
            if i == 0 {
                x = (tuple.0, m);
            } else {
                x = chinese(x, (tuple.0, m));
            }
        }
        let mut vec = self.line.iter().map(|(_, o)| *o).collect::<Vec<_>>();
        for _ in 0..=(x.1 + self.line.len()) {
            // if x.1 < t + self.line.len() {
            //     println!("{:>4}: {:?}", t, vec);
            // }
            for (i, v) in vec.iter_mut().enumerate() {
                *v = (*v + 1) % self.line[i].0;
            }
            // if t == x.1 {
            //     println!("-------------------");
            // }
        }
        x.1
    }
    fn part2(&mut self) -> usize {
        self.line.push((11, 0));
        let mut x = self.line[0];
        for (i, tuple) in self.line.iter().enumerate() {
            let mut m = (tuple.0 + tuple.1 + ((i + 1) % tuple.0)) % tuple.0;
            m = tuple.0 - m;
            // println!("周期{}で{}start", tuple.0, m);
            if i == 0 {
                x = (tuple.0, m);
            } else {
                x = chinese(x, (tuple.0, m));
            }
        }
        x.1
    }
}

/// Return `x` such that:
/// * x `mod` aq = ar
/// * x `mod` bq = br
///
/// ```
/// use crate::adventofcode::y2016::day15::*;
/// let a = chinese((5, 4), (2, 0));
/// assert_eq!(a.1, 14);
/// ```
pub fn chinese((aq, ar): (usize, usize), (bq, br): (usize, usize)) -> (usize, usize) {
    let n = solve1(aq, bq);
    let nar = (n * ar) % bq;
    let nbr = (n * br) % bq;
    let m = if nar < nbr {
        nbr - nar
    } else {
        (bq + nbr) - nar
    };
    (aq * bq, aq * m + ar)
}

/// Return `X` such that:
/// (X * a) `mod` m = ((X * b) `mod` m) + 1
///
fn solve1(a: usize, m: usize) -> usize {
    for i in 0.. {
        if (i * a) % m == 1 {
            return i;
        }
    }
    panic!("can't");
}
