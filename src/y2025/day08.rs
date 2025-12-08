//! <https://adventofcode.com/2025/day/8>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{AdventOfCode, ParseError, aoc},
        geometric::{Dim3, NeighborIter},
    },
    // rayon::prelude::*,
    rustc_data_structures::fx::{FxHashMap, FxHasher},
    // serde::Serialize,
    std::{
        cmp::{Ordering, Reverse},
        collections::{BinaryHeap, HashMap},
        hash::BuildHasherDefault,
    },
};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Dim3<usize>>,
}

mod parser {
    use {
        crate::{geometric::Dim3, parser::parse_usize},
        winnow::{
            ModalResult, Parser,
            ascii::{alpha1, newline, space1},
            combinator::{alt, separated, seq},
        },
    };

    fn parse_line(s: &mut &str) -> ModalResult<Dim3<usize>> {
        separated(1.., parse_usize, ",")
            .map(|v: Vec<usize>| (v[0], v[1], v[2]))
            .parse_next(s)
    }

    pub fn parse(s: &mut &str) -> ModalResult<Vec<Dim3<usize>>> {
        separated(1.., parse_line, newline).parse_next(s)
    }
}

#[aoc(2025, 8)]
impl AdventOfCode for Puzzle {
    fn prepare(&mut self, mut input: &str) -> Result<(), ParseError> {
        self.line = parser::parse(&mut input)?;
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut distances: HashMap<(usize, usize), usize> = HashMap::new();
        for (i, x) in self.line.iter().enumerate() {
            for (j, y) in self.line.iter().enumerate() {
                if i < j {
                    distances.insert(
                        (i, j),
                        x.0.abs_diff(y.0).pow(2)
                            + x.1.abs_diff(y.1).pow(2)
                            + x.2.abs_diff(y.2).pow(2),
                    );
                }
            }
        }
        let mut d = distances
            .iter()
            .map(|(pair, dist)| (*dist, *pair))
            .collect::<Vec<_>>();
        // let mut _: FxHashMap<_, _> = HashMap::<_, _, BuildHasherDefault<FxHasher>>::default();
        d.sort();
        dbg!(&d[0]);
        let mut membership: Vec<usize> = vec![0; self.line.len()];
        let mut new_group: usize = 0;
        for (_, (i, j)) in d.iter().take(1000) {
            let g1 = membership[*i];
            let g2 = membership[*j];
            match (g1 == 0, g2 == 0) {
                (false, false) => {
                    let merging_id = membership[*i];
                    let removing_id = membership[*j];
                    for i in membership.iter_mut() {
                        if *i == removing_id {
                            *i = merging_id;
                        }
                    }
                }
                (false, true) => {
                    membership[*j] = membership[*i];
                }
                (true, false) => {
                    membership[*i] = membership[*j];
                }
                (true, true) => {
                    dbg!(self.line[*i]);
                    dbg!(self.line[*j]);
                    new_group += 1;
                    membership[*i] = new_group;
                    membership[*j] = new_group;
                }
            }
        }
        let mut groups: HashMap<usize, Vec<usize>> = HashMap::new();
        for (i, g) in membership.iter().enumerate() {
            groups.entry(*g).or_default().push(i);
        }
        let mut gv = groups
            .iter()
            .map(|(id, l)| if *id == 0 { 1 } else { l.len() })
            .collect::<Vec<_>>();
        gv.sort();
        dbg!(&gv[gv.len() - 3..]);
        gv[gv.len() - 3..].iter().product()
    }
    fn part2(&mut self) -> Self::Output2 {
        2
    }
}
