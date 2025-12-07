//! <https://adventofcode.com/2025/day/7>
use {
    crate::{
        framework::{AdventOfCode, ParseError, aoc},
        geometric::Dim2,
    },
    rustc_data_structures::fx::{FxHashMap, FxHashSet, FxHasher},
    std::{
        collections::{HashMap, HashSet},
        hash::BuildHasherDefault,
    },
};

#[derive(Clone, Debug, Default)]
pub struct Puzzle {
    line: Vec<Vec<char>>,
    start: Dim2<usize>,
}

mod parser {
    use winnow::{
        ModalResult, Parser,
        ascii::newline,
        combinator::{repeat, separated},
        token::one_of,
    };

    fn parse_line(s: &mut &str) -> ModalResult<Vec<char>> {
        repeat(1.., one_of(['.', '^', 'S'])).parse_next(s)
    }
    pub fn parse(s: &mut &str) -> ModalResult<Vec<Vec<char>>> {
        separated(1.., parse_line, newline).parse_next(s)
    }
}

#[aoc(2025, 7)]
impl AdventOfCode for Puzzle {
    fn prepare(&mut self, mut input: &str) -> Result<(), ParseError> {
        self.line = parser::parse(&mut input)?;
        'end: for (i, l) in self.line.iter().enumerate() {
            for (j, c) in l.iter().enumerate() {
                if *c == 'S' {
                    self.start = (i, j);
                    break 'end;
                }
            }
        }
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        let height = self.line.len();
        let width = self.line[0].len();
        let mut pos: FxHashSet<usize> = HashSet::<usize, BuildHasherDefault<FxHasher>>::default();
        pos.insert(self.start.1);
        let mut next: FxHashSet<usize> = HashSet::<usize, BuildHasherDefault<FxHasher>>::default();
        let mut num_splits = 0;
        for y in self.start.0..height {
            next.clear();
            for x in pos.iter() {
                if self.line[y][*x] == '^' {
                    num_splits += 1;
                    if 0 < *x {
                        next.insert(x - 1);
                    }
                    if x + 1 < width {
                        next.insert(x + 1);
                    }
                } else {
                    next.insert(*x);
                }
            }
            std::mem::swap(&mut pos, &mut next);
        }
        num_splits
    }
    fn part2(&mut self) -> Self::Output2 {
        let height = self.line.len();
        let width = self.line[0].len();
        let mut pos: FxHashMap<usize, usize> =
            HashMap::<usize, usize, BuildHasherDefault<FxHasher>>::default();
        pos.insert(self.start.1, 1);
        let mut next: FxHashMap<usize, usize> =
            HashMap::<usize, usize, BuildHasherDefault<FxHasher>>::default();
        for y in self.start.0..height {
            next.clear();
            for (x, n) in pos.iter() {
                if self.line[y][*x] == '^' {
                    if 0 < *x {
                        *next.entry(x - 1).or_insert(0) += n;
                    }
                    if x + 1 < width {
                        *next.entry(x + 1).or_insert(0) += n;
                    }
                } else {
                    *next.entry(*x).or_insert(0) += n;
                }
            }
            std::mem::swap(&mut pos, &mut next);
        }
        pos.into_values().sum::<usize>()
    }
}
