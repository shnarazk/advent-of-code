//! <https://adventofcode.com/2025/day/8>
use {
    crate::{
        framework::{AdventOfCode, ParseError, aoc},
        geometric::Dim3,
    },
    rayon::prelude::*,
    std::collections::{BinaryHeap, HashMap},
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
        let size = self.line.len();
        /*
        let mut d = (0..size)
            .into_par_iter()
            .flat_map(|i| {
                (i + 1..size)
                    .into_par_iter()
                    .map(|j| {
                        let x = self.line[i];
                        let y = self.line[j];
                        (
                            [
                                x.0.abs_diff(y.0).pow(2),
                                x.1.abs_diff(y.1).pow(2),
                                x.2.abs_diff(y.2).pow(2),
                            ]
                            .iter()
                            .sum::<usize>(),
                            (i, j),
                        )
                    })
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        d.sort();
        */
        let mut heap: BinaryHeap<(usize, (usize, usize))> = BinaryHeap::new();
        for (i, x) in self.line.iter().enumerate() {
            for (j, y) in self.line.iter().enumerate().skip(i + 1) {
                let r = (
                    [
                        x.0.abs_diff(y.0).pow(2),
                        x.1.abs_diff(y.1).pow(2),
                        x.2.abs_diff(y.2).pow(2),
                    ]
                    .iter()
                    .sum::<usize>(),
                    (i, j),
                );
                if heap.len() < limit {
                    heap.push(r);
                } else if r.0 < heap.peek().map_or(usize::MAX, |r| r.0) {
                    heap.pop();
                    heap.push(r);
                }
            }
        }
        let d = heap.into_sorted_vec();
        assert_eq!(d.len(), limit);
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
                    // assert_eq!(new_group, group_heap.len() - 1);
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
        let size = self.line.len();
        let mut d = (0..size)
            .into_par_iter()
            .flat_map(|i| {
                (i + 1..size)
                    .into_par_iter()
                    .map(|j| {
                        let x = self.line[i];
                        let y = self.line[j];
                        (
                            [
                                x.0.abs_diff(y.0).pow(2),
                                x.1.abs_diff(y.1).pow(2),
                                x.2.abs_diff(y.2).pow(2),
                            ]
                            .iter()
                            .sum::<usize>(),
                            (i, j),
                        )
                    })
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        d.sort();
        let mut group_heap: Vec<usize> = vec![0];
        let mut membership: Vec<usize> = vec![0; self.line.len()];
        let mut new_group: usize = 0;
        let mut num_groups = 0;
        for (_, (i, j)) in d.iter() {
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
                    group_heap.push(0);
                    membership[*i] = new_group;
                    membership[*j] = new_group;
                }
            }
            if num_groups == 1 && membership.iter().filter(|g| **g != 0).count() == self.line.len()
            {
                return self.line[*i].0 * self.line[*j].0;
            }
        }
        unreachable!()
    }
}
