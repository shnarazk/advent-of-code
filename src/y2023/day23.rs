//! <https://adventofcode.com/2023/day/23>
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::{Dim2, GeometricMath},
        progress,
    },
    std::collections::{BinaryHeap, HashMap, HashSet},
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Vec<u8>>,
    sum_path: Vec<Vec<usize>>,
    path_index: Vec<Vec<Option<usize>>>,
    vector_template: Vec<bool>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
struct Route {
    cost: usize,
    pos: Dim2<usize>,
    pre: Dim2<usize>,
    used: Vec<usize>,
    size: Dim2<usize>,
}

#[aoc(2023, 23)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.line.push(block.bytes().collect::<Vec<_>>());
        Ok(())
    }
    fn end_of_data(&mut self) {
        self.sum_path = self
            .line
            .iter()
            .map(|v| v.iter().map(|p| (*p != b'#') as usize).collect::<Vec<_>>())
            .collect::<Vec<_>>();
        for (y, l) in self.line.iter().enumerate() {
            for (x, _) in l.iter().enumerate() {
                self.sum_path[y][x] += if y == 0 { 0 } else { self.sum_path[y - 1][x] }
                    + if x == 0 { 0 } else { self.sum_path[y][x - 1] };
            }
        }
        let pathes = self
            .line
            .iter()
            .enumerate()
            .flat_map(|(y, l)| {
                l.iter()
                    .enumerate()
                    .flat_map(|(x, p)| (*p != b'#').then_some((y, x)))
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        self.path_index = self
            .line
            .iter()
            .map(|v| v.iter().map(|_| None).collect::<Vec<_>>())
            .collect::<Vec<_>>();
        self.vector_template = Vec::new();
        for (i, (y, x)) in pathes.iter().enumerate() {
            self.path_index[*y][*x] = Some(i);
            self.vector_template.push(false);
        }
        // dbg!(&self.line);
    }
    fn part1(&mut self) -> Self::Output1 {
        let height = self.line.len();
        let width = self.line[0].len();
        let goal = (height - 1, width - 2);
        let mut to_visit: Vec<(Dim2<usize>, HashSet<Dim2<usize>>)> = vec![];
        let mut longest = 0;
        to_visit.push(((0, 1), HashSet::new()));
        while let Some(p) = to_visit.pop() {
            if p.0 == goal {
                longest = longest.max(p.1.len());
                continue;
            }
            for q0 in p.0.neighbors4((0, 0), (height, width)).iter_mut() {
                let mut q = p.clone();
                match self.line[q0.0][q0.1] {
                    b'^' => {
                        q.1.insert(*q0);
                        q0.0 -= 1;
                    }
                    b'<' => {
                        q.1.insert(*q0);
                        q0.1 -= 1;
                    }
                    b'>' => {
                        q.1.insert(*q0);
                        q0.1 += 1;
                    }
                    b'v' => {
                        q.1.insert(*q0);
                        q0.0 += 1;
                    }
                    _ => (),
                }
                if self.line[q0.0][q0.1] != b'#' && !p.1.contains(q0) {
                    q.0 = *q0;
                    q.1.insert(*q0);
                    to_visit.push(q);
                }
            }
        }
        longest
    }
    // This is not a variant of shortest path finding problem, for which
    // we should make a heuristc evaluation.
    // Instead We should cut the unused path as pre-processing task.
    fn part2(&mut self) -> Self::Output2 {
        let height = self.line.len();
        let width = self.line[0].len();
        let goal = (height - 1, width - 2);
        let mut to_visit: BinaryHeap<Route> = BinaryHeap::new();
        let mut longest = 0;
        to_visit.push(Route {
            cost: 1,
            pos: (0, 1),
            pre: (0, 0),
            used: Vec::new(),
            size: (1, 1),
        });
        let mut visited: HashMap<Vec<usize>, usize> = HashMap::new();
        while let Some(mut p) = to_visit.pop() {
            if p.pos == goal {
                if longest < p.cost {
                    longest = p.cost;
                    progress!(longest);
                }
                continue;
            }
            if p.used.contains(&self.path_index[p.pos.0][p.pos.1].unwrap()) {
                continue;
            }
            let next = p
                .pos
                .neighbors4((0, 0), (height, width))
                .into_iter()
                .filter(|(y, x)| self.line[*y][*x] != b'#')
                .filter(|(y, x)| p.pre != (*y, *x))
                .collect::<Vec<_>>();
            let at_branch = 1 < next.len();
            if at_branch {
                if let Some(k) = visited.get(&p.used) {
                    if p.cost < *k {
                        continue;
                    }
                }
                p.used.push(self.path_index[p.pos.0][p.pos.1].unwrap());
                visited.insert(p.used.clone(), p.cost);
            }
            for q0 in next.iter() {
                let mut q = p.clone();
                q.cost += 1;
                q.pos = *q0;
                q.pre = p.pos;
                q.size.0 = q.size.0.max(q0.0);
                q.size.1 = q.size.1.max(q0.1);
                to_visit.push(q);
            }
        }
        progress!("");
        longest - 1
    }
}

#[allow(dead_code)]
fn check_branches(v: &[Vec<u8>]) -> usize {
    let height = v.len();
    let width = v[0].len();
    v.iter()
        .enumerate()
        .map(|(y, l)| {
            l.iter()
                .enumerate()
                .filter(|(x, p)| {
                    2 < (y, *x)
                        .neighbors4((0, 0), (height, width))
                        .into_iter()
                        .filter(|_| **p != b'#')
                        .filter(|(y, x)| v[*y][*x] != b'#')
                        .count()
                })
                .count()
        })
        .sum()
}
