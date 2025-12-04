//! <https://adventofcode.com/2025/day/4>
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::{neighbors8, Dim2},
    },
    rustc_data_structures::fx::{FxHashMap, FxHashSet, FxHasher},
    std::{
        collections::{hash_map::Entry, HashMap, HashSet},
        hash::BuildHasherDefault,
        mem::swap,
    },
};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Vec<bool>>,
}

mod parser {
    use winnow::{
        ascii::newline,
        combinator::{repeat, separated},
        token::one_of,
        ModalResult, Parser,
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
        let mut propagate: FxHashMap<Dim2<usize>, Vec<Dim2<usize>>> =
            HashMap::<_, _, BuildHasherDefault<FxHasher>>::default();
        let mut count: FxHashMap<Dim2<usize>, u8> =
            HashMap::<_, _, BuildHasherDefault<FxHasher>>::default();
        for (i, l) in self.line.iter().enumerate() {
            for (j, b) in l.iter().enumerate() {
                if *b {
                    neighbors8(i, j, height, width)
                        .iter()
                        .filter(|p| self.line[p.0][p.1])
                        .for_each(|p| {
                            propagate.entry((i, j)).or_default().push(*p);
                            *count.entry((i, j)).or_insert(0) += 1;
                        });
                    if let Entry::Vacant(e) = count.entry((i, j)) {
                        e.insert(0);
                        propagate.insert((i, j), Vec::new());
                    }
                }
            }
        }
        let amount = count.len();
        let mut removables: FxHashSet<Dim2<usize>> =
            HashSet::<_, BuildHasherDefault<FxHasher>>::default();
        for (p, c) in count.iter() {
            if *c < 4 {
                removables.insert(*p);
            }
        }
        let mut next: FxHashSet<Dim2<usize>> =
            HashSet::<_, BuildHasherDefault<FxHasher>>::default();
        while !removables.is_empty() {
            next.clear();
            for p in removables.iter() {
                if count.contains_key(p) {
                    count.remove(p);
                    for q in propagate.get(p).unwrap().iter() {
                        if let Some(n) = count.get_mut(q) {
                            *n -= 1;
                            if *n < 4 {
                                next.insert(*q);
                            }
                        }
                    }
                }
            }
            swap(&mut next, &mut removables);
        }
        amount - count.len()
    }
}
