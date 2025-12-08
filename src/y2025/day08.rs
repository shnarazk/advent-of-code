//! <https://adventofcode.com/2025/day/8>
use {
    crate::{
        framework::{AdventOfCode, ParseError, aoc},
        geometric::Dim3,
    },
    rustc_data_structures::fx::{FxHashMap, FxHasher},
    std::{collections::HashMap, hash::BuildHasherDefault},
};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Dim3<usize>>,
}

mod parser {
    use {
        crate::{geometric::Dim3, parser::parse_usize},
        winnow::{ModalResult, Parser, ascii::newline, combinator::separated},
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
        let limit = self
            .get_config()
            .alt
            .as_ref()
            .map_or(1000_usize, |_| 10_usize);
        let mut distances: FxHashMap<(usize, usize), usize> =
            HashMap::<_, _, BuildHasherDefault<FxHasher>>::default();
        // TODO: use rayon!
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
        d.sort();
        let mut group_heap: Vec<usize> = vec![0];
        let mut membership: Vec<usize> = vec![0; self.line.len()];
        let mut new_group: usize = 0;
        for (_, (i, j)) in d.iter().take(limit) {
            let mut g1 = membership[*i];
            while group_heap[g1] != 0 {
                g1 = group_heap[g1];
            }
            let mut g2 = membership[*j];
            while group_heap[g2] != 0 {
                g2 = group_heap[g2];
            }
            match (g1 == 0, g2 == 0) {
                (false, false) => {
                    if g1 != g2 {
                        let a = g1.min(g2);
                        let b = g1.max(g2);
                        group_heap[b] = a;
                    }
                }
                (false, true) => {
                    membership[*j] = membership[*i];
                }
                (true, false) => {
                    membership[*i] = membership[*j];
                }
                (true, true) => {
                    new_group += 1;
                    group_heap.push(0);
                    assert_eq!(new_group, group_heap.len() - 1);
                    membership[*i] = new_group;
                    membership[*j] = new_group;
                }
            }
        }
        let mut groups: HashMap<usize, Vec<usize>> = HashMap::new();
        for (i, rg) in membership.iter().enumerate() {
            let mut g = *rg;
            while group_heap[g] != 0 {
                g = group_heap[g];
            }
            groups.entry(g).or_default().push(i);
        }
        let mut gv = groups
            .iter()
            .map(|(id, l)| if *id == 0 { 1 } else { l.len() })
            .collect::<Vec<_>>();
        gv.sort();
        gv[gv.len() - 3..].iter().product()
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut distances: FxHashMap<(usize, usize), usize> =
            HashMap::<_, _, BuildHasherDefault<FxHasher>>::default();
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
        d.sort();
        let mut membership: Vec<usize> = vec![0; self.line.len()];
        let mut new_group: usize = 0;
        let mut num_groups = 0;
        for (_, (i, j)) in d.iter() {
            let g1 = membership[*i];
            let g2 = membership[*j];
            match (g1 == 0, g2 == 0) {
                (false, false) => {
                    if g1 != g2 {
                        let merging_id = membership[*i];
                        let removing_id = membership[*j];
                        for i in membership.iter_mut() {
                            if *i == removing_id {
                                *i = merging_id;
                            }
                        }
                        num_groups -= 1;
                    }
                }
                (false, true) => {
                    membership[*j] = membership[*i];
                }
                (true, false) => {
                    membership[*i] = membership[*j];
                }
                (true, true) => {
                    new_group += 1;
                    num_groups += 1;
                    membership[*i] = new_group;
                    membership[*j] = new_group;
                }
            }
            if num_groups == 1 && membership.iter().filter(|g| **g != 0).count() == self.line.len()
            {
                return self.line[*i].0 * self.line[*j].0;
            }
        }
        0
    }
}
