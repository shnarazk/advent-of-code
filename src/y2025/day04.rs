//! <https://adventofcode.com/2025/day/4>
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::Dim2,
    },
    rustc_data_structures::fx::{FxHashMap, FxHashSet, FxHasher},
    std::{
        collections::{HashMap, HashSet},
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
                if *b {
                    let mut count = 0;
                    for r in 0..8 {
                        let q = match r {
                            0 if 0 < i && 0 < j => (i - 1, j - 1),
                            1 if 0 < i => (i - 1, j),
                            2 if 0 < i && j < width - 1 => (i - 1, j + 1),
                            3 if 0 < j => (i, j - 1),
                            4 if j < width - 1 => (i, j + 1),
                            5 if i < height - 1 && 0 < j => (i + 1, j - 1),
                            6 if i < height - 1 => (i + 1, j),
                            7 if i < height - 1 && j < width - 1 => (i + 1, j + 1),
                            _ => continue,
                        };
                        if self.line[q.0][q.1] {
                            count += 1;
                        }
                    }
                    if count < 4 {
                        found += 1;
                    }
                }
            }
        }
        found
    }
    fn part2(&mut self) -> Self::Output2 {
        let height = self.line.len();
        let width = self.line[0].len();
        let num_rolls = self
            .line
            .iter()
            .map(|l| l.iter().filter(|b| **b).count())
            .sum();
        let mut roll_id: FxHashMap<Dim2<usize>, usize> =
            HashMap::<_, _, BuildHasherDefault<FxHasher>>::default();
        let mut propagate = vec![Vec::<usize>::new(); num_rolls];
        let mut count = vec![1_u8; num_rolls]; // 0 for dead
        for (i, l) in self.line.iter().enumerate() {
            for (j, b) in l.iter().enumerate() {
                if *b {
                    let n = roll_id.len();
                    let p_id = *roll_id.entry((i, j)).or_insert(n);
                    for r in 0..8 {
                        let q = match r {
                            0 if 0 < i && 0 < j => (i - 1, j - 1),
                            1 if 0 < i => (i - 1, j),
                            2 if 0 < i && j < width - 1 => (i - 1, j + 1),
                            3 if 0 < j => (i, j - 1),
                            4 if j < width - 1 => (i, j + 1),
                            5 if i < height - 1 && 0 < j => (i + 1, j - 1),
                            6 if i < height - 1 => (i + 1, j),
                            7 if i < height - 1 && j < width - 1 => (i + 1, j + 1),
                            _ => continue,
                        };
                        if self.line[q.0][q.1] {
                            let n = roll_id.len();
                            let q_id = *roll_id.entry(q).or_insert(n);
                            propagate[p_id].push(q_id);
                            count[p_id] += 1;
                        }
                    }
                }
            }
        }
        let mut removables: FxHashSet<usize> =
            HashSet::<_, BuildHasherDefault<FxHasher>>::default();
        for (id, c) in count.iter().enumerate() {
            if *c < 4 + 1 {
                removables.insert(id);
            }
        }
        let mut next: FxHashSet<usize> = HashSet::<_, BuildHasherDefault<FxHasher>>::default();
        let mut num_deads = 0;
        while !removables.is_empty() {
            next.clear();
            for p in removables.iter() {
                if count[*p] > 0 {
                    count[*p] = 0;
                    num_deads += 1;
                    for q in propagate[*p].iter() {
                        if count[*q] > 0 {
                            count[*q] -= 1;
                            if count[*q] < 4 + 1 {
                                next.insert(*q);
                            }
                        }
                    }
                }
            }
            swap(&mut next, &mut removables);
        }
        num_deads
    }
}
