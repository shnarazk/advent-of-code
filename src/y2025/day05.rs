//! <https://adventofcode.com/2025/day/5>
use {
    crate::framework::{AdventOfCode, ParseError, aoc},
    rustc_data_structures::fx::{FxHashMap, FxHasher},
    std::{collections::HashMap, hash::BuildHasherDefault},
};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    // 1. inclsive: closed range
    // 2. overlapped
    ranges: Vec<(usize, usize)>,
    // if it is in a range, it's called 'fresh'
    availables: Vec<usize>,
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

    fn parse_two_usizes(s: &mut &str) -> ModalResult<(usize, usize)> {
        seq!(parse_usize, "-", parse_usize)
            .parse_next(s)
            .map(|(a, _, b)| (a, b))
    }

    fn parse_block1(s: &mut &str) -> ModalResult<Vec<(usize, usize)>> {
        separated(1.., parse_two_usizes, newline).parse_next(s)
    }
    fn parse_block2(s: &mut &str) -> ModalResult<Vec<usize>> {
        separated(1.., parse_usize, newline).parse_next(s)
    }

    pub fn parse(s: &mut &str) -> ModalResult<(Vec<(usize, usize)>, Vec<usize>)> {
        seq!(parse_block1, seq!(newline, newline), parse_block2)
            .parse_next(s)
            .map(|(a, _, b)| (a, b))
    }
}

#[aoc(2025, 5)]
impl AdventOfCode for Puzzle {
    fn prepare(&mut self, mut input: &str) -> Result<(), ParseError> {
        let (b1, b2) = parser::parse(&mut input)?;
        self.ranges = b1;
        self.availables = b2;
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        self.availables
            .iter()
            .filter(|id| self.ranges.iter().any(|(b, e)| *b <= **id && **id <= *e))
            .count()
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut tick: FxHashMap<usize, (usize, usize)> =
            HashMap::<_, _, BuildHasherDefault<FxHasher>>::default();
        for (b, e) in self.ranges.iter() {
            let entry = tick.entry(*b).or_insert((0, 0));
            entry.0 += 1;
            let entry = tick.entry(*e).or_insert((0, 0));
            entry.1 += 1;
        }
        let mut v = tick.into_iter().collect::<Vec<_>>();
        v.sort();
        let mut count = 0;
        let mut nest = 0;
        let mut start = 0;
        for (n, (b, e)) in v.into_iter() {
            if 0 < b {
                if nest == 0 {
                    start = n;
                }
                nest += b;
            }
            if 0 < e {
                nest -= e;
                if nest == 0 {
                    count += n + 1 - start;
                }
            }
        }
        count
    }
}
