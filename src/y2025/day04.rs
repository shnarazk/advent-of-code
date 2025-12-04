//! <https://adventofcode.com/2025/day/4>
use {
    crate::{
        framework::{AdventOfCode, ParseError, aoc},
        geometric::{Dim2, neighbors8},
    },
    // rayon::prelude::*,
    rustc_data_structures::fx::{FxHashSet, FxHasher},
    // serde::Serialize,
    std::{collections::HashSet, hash::BuildHasherDefault, mem::swap},
};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Vec<bool>>,
}

mod parser {
    use winnow::{
        ModalResult, Parser,
        ascii::newline,
        combinator::{repeat, separated},
        token::one_of,
    };

    fn parse_line(s: &mut &str) -> ModalResult<Vec<bool>> {
        repeat(1.., one_of(['.', '@']).map(|c: char| c == '@')).parse_next(s)
    }
    pub fn parse(s: &mut &str) -> ModalResult<Vec<Vec<bool>>> {
        separated(1.., parse_line, newline).parse_next(s)
    }
}

#[aoc(2025, 4)]
impl AdventOfCode for Puzzle {
    fn prepare(&mut self, mut input: &str) -> Result<(), ParseError> {
        self.line = parser::parse(&mut input)?;
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut found: usize = 0;
        let height = self.line.len();
        let width = self.line[0].len();
        for (i, l) in self.line.iter().enumerate() {
            for (j, b) in l.iter().enumerate() {
                if *b
                    && neighbors8(i, j, height, width)
                        .iter()
                        .filter(|(i, j)| self.line[*i][*j])
                        .count()
                        < 4
                {
                    found += 1;
                }
            }
        }
        found
    }
    fn part2(&mut self) -> Self::Output2 {
        let height = self.line.len();
        let width = self.line[0].len();
        let mut state: FxHashSet<Dim2<usize>> =
            HashSet::<_, BuildHasherDefault<FxHasher>>::default();
        for (i, l) in self.line.iter().enumerate() {
            for (j, b) in l.iter().enumerate() {
                if *b {
                    state.insert((i, j));
                }
            }
        }
        let amount = state.len();
        let mut work: FxHashSet<Dim2<usize>> =
            HashSet::<_, BuildHasherDefault<FxHasher>>::default();
        let mut proceed: bool = true;
        while proceed {
            proceed = false;
            work.clear();
            for pos in state.iter() {
                if neighbors8(pos.0, pos.1, height, width)
                    .iter()
                    .filter(|p| state.contains(p))
                    .count()
                    < 4
                {
                    proceed = true;
                } else {
                    work.insert((pos.0, pos.1));
                }
            }
            swap(&mut work, &mut state);
        }
        amount - state.len()
    }
}
