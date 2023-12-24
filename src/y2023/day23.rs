//! <https://adventofcode.com/2023/day/23>
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::{Dim2, GeometricMath},
        progress,
    },
    std::collections::{BinaryHeap, HashSet},
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Vec<u8>>,
    sum_path: Vec<Vec<usize>>,
    path_index: Vec<Vec<Option<usize>>>,
    num_path: usize,
    vector_template: Vec<bool>,
}

#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
struct Route {
    // estimate: f64,
    visited: usize,
    pos: Dim2<usize>,
    map: Vec<bool>,
}

impl PartialOrd for Route {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.visited.cmp(&other.visited))
    }
}

impl Ord for Route {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.visited.cmp(&other.visited)
    }
}

// impl PartialEq for Route {
//     fn eq(&self, other: &Self) -> bool {
//         self.pos.eq(&other.pos) && self.map.eq(&other.map)
//     }
// }

// impl Eq for Route {}

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
                    .flat_map(|(x, p)| (*p != b'#').then(|| (y, x)))
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
        self.num_path = pathes.len();
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
    fn part2(&mut self) -> Self::Output2 {
        let height = self.line.len();
        let width = self.line[0].len();
        let goal = (height - 1, width - 2);
        let mut to_visit: BinaryHeap<Route> = BinaryHeap::new();
        let mut longest = 0;
        // let accessables = self
        //     .line
        //     .iter()
        //     .map(|v| v.iter().filter(|p| **p != b'#').count())
        //     .sum::<usize>();
        to_visit.push(Route {
            visited: 1,
            pos: (0, 1),
            map: self.vector_template.clone(), // self.line.iter().map(|l| l.iter().map(||)),
        });
        let mut visited: HashSet<Route> = HashSet::new();
        while let Some(p) = to_visit.pop() {
            if visited.contains(&p) {
                continue;
            }
            if to_visit.len() % 20 == 0 {
                progress!(visited.len());
            }
            if p.pos == goal {
                if longest < p.visited {
                    longest = dbg!(p.visited);
                }
                continue;
            }
            if visited.contains(&p) {
                continue;
            }
            // let estimate = self.sum_path[p.pos.0][p.pos.1] as f64
            //     / p.map
            //         .iter()
            //         .filter(|(y, x)| *y <= p.pos.0 && *x <= p.pos.1)
            //         .count() as f64;
            let iter = p
                .pos
                .neighbors4((0, 0), (height, width))
                .into_iter()
                .filter(|(y, x)| {
                    self.line[*y][*x] != b'#' && !p.map[self.path_index[*y][*x].unwrap()]
                })
                .collect::<Vec<_>>();
            let at_branch = 1 < iter.len();
            if at_branch {
                visited.insert(p.clone());
            }
            for q0 in iter.iter() {
                let mut q = p.clone();
                // q.estimate = estimate;
                q.visited += 1;
                q.pos = *q0;
                q.map[self.path_index[q0.0][q0.1].unwrap()] = true;
                // q.map.insert(*q0);
                to_visit.push(q);
            }
        }
        longest
    }
}
