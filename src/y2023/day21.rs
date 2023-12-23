//! <https://adventofcode.com/2023/day/21>
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::{Dim2, GeometricMath},
        progress,
    },
    std::collections::HashSet,
};

const LIMIT: usize = 26501365;

#[derive(Debug, Default, Eq, PartialEq)]
pub struct Puzzle {
    line: Vec<Vec<bool>>,
    start: Dim2<usize>,
    cycle_len: usize,
}

#[aoc(2023, 21)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        if let Some(i) = block.chars().enumerate().find(|(_, c)| *c == 'S') {
            self.start = (self.line.len(), i.0);
        }
        self.line
            .push(block.chars().map(|c| c == '#').collect::<Vec<_>>());
        Ok(())
    }
    fn end_of_data(&mut self) {
        let height = self.line.len();
        let width = self.line[0].len();
        self.cycle_len = height + width;
        // for l in self.line.iter_mut() { for p in l.iter_mut() { *p = false; } }
    }
    fn part1(&mut self) -> Self::Output1 {
        let steps = 64;
        let height = self.line.len();
        let width = self.line[0].len();
        let mut to_visit: Vec<Dim2<usize>> = Vec::new();
        let mut next: Vec<Dim2<usize>> = Vec::new();
        to_visit.push(self.start);
        let mut map = self
            .line
            .iter()
            .map(|l| l.iter().map(|_| usize::MAX).collect::<Vec<_>>())
            .collect::<Vec<_>>();
        for n in 0..=steps {
            while let Some(p) = to_visit.pop() {
                if !self.line[p.0][p.1] {
                    map[p.0][p.1] = n;
                    for q in p.neighbors4((0, 0), (height, width)).iter() {
                        if !next.contains(q) {
                            next.push(*q);
                        }
                    }
                }
            }
            std::mem::swap(&mut to_visit, &mut next);
        }
        map.iter()
            .map(|l| l.iter().filter(|c| **c == steps).count())
            .sum::<usize>()
    }
    fn part2(&mut self) -> Self::Output1 {
        let mirrors = {
            let mut m = self.line.clone();
            m.rotate_left(self.start.0);
            for each in m.iter_mut() {
                each.rotate_left(self.start.1);
            }
            [
                m.clone(),
                {
                    let mut r = m.clone();
                    r.reverse();
                    r.rotate_right(1);
                    r
                },
                {
                    m.iter()
                        .map(|v| {
                            let mut w = v.clone();
                            w.reverse();
                            w.rotate_right(1);
                            w
                        })
                        .collect::<Vec<_>>()
                },
                {
                    let mut n = m
                        .iter()
                        .map(|v| {
                            let mut w = v.clone();
                            w.reverse();
                            w.rotate_right(1);
                            w
                        })
                        .collect::<Vec<_>>();
                    n.reverse();
                    n.rotate_right(1);
                    n
                },
            ]
        };
        let nrepeat = dbg!(LIMIT) / dbg!(self.cycle_len);
        let remaining_time = if 1 < nrepeat {
            LIMIT - nrepeat * self.cycle_len
        } else {
            LIMIT
        };
        // repeat for x > 0 and repeat for y > 0 == nrepeat
        let fullfilled = if 1 < nrepeat {
            (nrepeat * (nrepeat - 1)) / 2
        } else {
            0
        };
        let map_height = self.line.len();
        let map_width = self.line[0].len();
        let comp_fill: usize = 2 * self
            .line
            .iter()
            .map(|v| v.iter().filter(|b| !*b).count())
            .sum::<usize>();
        dbg!(nrepeat, fullfilled, remaining_time, comp_fill);
        dbg!(comp_fill * fullfilled);
        let maxfil = (LIMIT + 1).pow(2)
            - fullfilled
                * 2
                * self
                    .line
                    .iter()
                    .map(|v| v.iter().filter(|b| **b).count())
                    .sum::<usize>();
        println!("MxFil: {}", maxfil);
        let n_simulate = if 1 < nrepeat {
            self.cycle_len + remaining_time
        } else {
            remaining_time
        };
        mirrors
            .iter()
            .map(|m| {
                let mut to_visit: HashSet<Dim2<usize>> = HashSet::new();
                let mut next: HashSet<Dim2<usize>> = HashSet::new();
                to_visit.insert((0, 0));
                for n in 1..=n_simulate {
                    progress!(n);
                    for p in to_visit.iter() {
                        for q in p
                            .neighbors4((0, 0), (2 * self.cycle_len, 2 * self.cycle_len))
                            .iter()
                        {
                            if (!m[q.0 % map_height][q.1 % map_width]) && !next.contains(q) {
                                next.insert(*q);
                            }
                        }
                    }
                    to_visit.clear();
                    std::mem::swap(&mut to_visit, &mut next);
                }
                let incomp = to_visit.len();
                let incomp1 = to_visit
                    .iter()
                    .filter(|(x, y)| *x < self.cycle_len && *y < self.cycle_len)
                    .count();
                let incomp2 = (incomp - incomp1) / 2;
                dbg!(incomp, incomp1);
                assert!(to_visit
                    .iter()
                    .all(|(x, y)| !(self.cycle_len <= *x && self.cycle_len <= *y)));
                let result = match nrepeat {
                    0 | 1 => incomp,
                    m => fullfilled * comp_fill + incomp1 * m + incomp2 * (m + 1),
                } - (LIMIT + 1);
                dbg!(result)
            })
            .sum::<usize>()
            + 2 * (LIMIT + 1)
    }
}
