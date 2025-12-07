//! <https://adventofcode.com/2023/day/21>
use {
    crate::{
        framework::{AdventOfCode, ParseError, aoc},
        geometric::{Dim2, NeighborIter},
        progress,
    },
    std::collections::HashSet,
};

const LIMIT: usize = 26501365;

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Puzzle {
    line: Vec<Vec<bool>>,
    start: Dim2<usize>,
    cycle_len: usize,
}

#[aoc(2023, 21)]
impl AdventOfCode for Puzzle {
    fn prepare(&mut self, input: &str) -> Result<(), ParseError> {
        for l in input.lines() {
            if let Some(i) = l.chars().enumerate().find(|(_, c)| *c == 'S') {
                self.start = (self.line.len(), i.0);
            }
            self.line
                .push(l.chars().map(|c| c == '#').collect::<Vec<_>>());
        }
        let height = self.line.len();
        let width = self.line[0].len();
        self.cycle_len = height + width;
        Ok(())
    }
    fn serialize(&self) -> Option<String> {
        serde_json::to_string(&self.line).ok()
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
                    for q in p.iter4(&(height, width)) {
                        if !next.contains(&q) {
                            next.push(q);
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
        let nrepeat = dbg!(LIMIT) / dbg!(self.cycle_len);
        let (remaining_time, fullfilled, n_simulate) = if 1 < nrepeat {
            (
                LIMIT % self.cycle_len,
                (nrepeat * (nrepeat - 1)) / 2,
                self.cycle_len + LIMIT % self.cycle_len,
            )
        } else {
            (LIMIT, 0, LIMIT)
        };
        let comp_fill = 2 * self.reachable(&self.line);
        dbg!(nrepeat, fullfilled, remaining_time, comp_fill);
        // println!("Maxmum:  {}", self.max_fill(fullfilled));
        build_mirrors(shift(
            &self.line,
            (self.start.0 as isize, self.start.1 as isize),
        ))
        .iter()
        .map(|m| {
            let state = self.propagete_on(m, n_simulate);
            let incomp = state.len();
            let incomp1 = state
                .iter()
                .filter(|(x, y)| *x < self.cycle_len && *y < self.cycle_len)
                .count();
            let incomp2 = (incomp - incomp1) / 2;
            if 1 < nrepeat {
                fullfilled * comp_fill + incomp1 * nrepeat + incomp2 * (nrepeat + 1)
            } else {
                incomp
            }
        })
        .sum::<usize>()
            - 2 * (LIMIT + 1)
    }
}
fn build_mirrors(v: Vec<Vec<bool>>) -> [Vec<Vec<bool>>; 4] {
    let m = v.to_vec();
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
}
impl Puzzle {
    fn propagete_on(&self, map: &[Vec<bool>], upto: usize) -> HashSet<Dim2<usize>> {
        let height = map.len();
        let width = map[0].len();
        let mut to_visit: HashSet<Dim2<usize>> = HashSet::new();
        let mut next: HashSet<Dim2<usize>> = HashSet::new();
        to_visit.insert((0, 0));
        for n in 1..=upto {
            progress!(n);
            for p in to_visit.iter() {
                for q in p.iter4(&(2 * self.cycle_len, 2 * self.cycle_len)) {
                    if (!map[q.0 % height][q.1 % width]) && !next.contains(&q) {
                        next.insert(q);
                    }
                }
            }
            to_visit.clear();
            std::mem::swap(&mut to_visit, &mut next);
        }
        to_visit
    }
    fn reachable(&self, map: &[Vec<bool>]) -> usize {
        let height = map.len();
        let width = map[0].len();
        let mut to_visit: Vec<Dim2<usize>> = Vec::new();
        let mut m = map
            .iter()
            .map(|v| v.iter().map(|b| *b as usize).collect::<Vec<_>>())
            .collect::<Vec<_>>();
        to_visit.push((0, 0));
        while let Some(p) = to_visit.pop() {
            if m[p.0][p.1] == 0 {
                m[p.0][p.1] = 2;
            }
            for q in p.iter4(&(height, width)) {
                if (m[q.0][q.1] == 0) && !to_visit.contains(&q) {
                    to_visit.push(q);
                }
            }
        }
        m.iter()
            .map(|v| v.iter().filter(|n| **n == 2).count())
            .sum()
    }
    #[allow(dead_code)]
    fn max_fill(&self, fullfilled: usize) -> usize {
        (LIMIT + 1).pow(2)
            - fullfilled
                * 2
                * self
                    .line
                    .iter()
                    .map(|v| v.iter().filter(|b| **b).count())
                    .sum::<usize>()
    }
}

fn shift(matrix: &[Vec<bool>], p: Dim2<isize>) -> Vec<Vec<bool>> {
    let mut m = matrix.to_vec();
    if p.0 < 0 {
        m.rotate_left(-p.0 as usize);
    } else {
        m.rotate_left(p.0 as usize);
    }
    for each in m.iter_mut() {
        if p.0 < 0 {
            each.rotate_left(-p.1 as usize);
        } else {
            each.rotate_left(p.1 as usize);
        }
    }
    m
}
