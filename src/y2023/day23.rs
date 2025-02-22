//! <https://adventofcode.com/2023/day/23>
use {
    crate::{
        framework::{AdventOfCode, ParseError, aoc},
        geometric::{Dim2, GeometricMath},
        progress,
    },
    serde::Serialize,
    std::{
        cmp::Reverse,
        collections::{BinaryHeap, HashMap, HashSet, hash_map::Entry},
    },
};

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Puzzle {
    line: Vec<Vec<u8>>,
    size: Dim2<usize>,
    branch_index: Vec<Vec<Option<usize>>>,
    branch_positions: Vec<Dim2<usize>>,
    branch_graph: Vec<Vec<usize>>,
    solution: Option<Route>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct Route {
    cost: usize,
    pos: usize,
    used: Vec<usize>,
}

impl PartialOrd for Route {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cost.cmp(&other.cost))
    }
}

impl Ord for Route {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.cost.cmp(&other.cost)
    }
}

#[aoc(2023, 23)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, input: &str) -> Result<(), ParseError> {
        self.line = input
            .lines()
            .map(|l| l.bytes().collect::<Vec<_>>())
            .collect::<Vec<_>>();
        self.size = (self.line.len(), self.line[0].len());
        let branching = self.branch_map();
        self.branch_positions = self
            .line
            .iter()
            .enumerate()
            .flat_map(|(y, l)| {
                l.iter()
                    .enumerate()
                    .flat_map(|(x, _)| (2 < branching[y][x]).then_some((y, x)))
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        // inject the start and the goal
        self.branch_positions.insert(0, (0, 1));
        self.branch_positions
            .push((self.size.0 - 1, self.size.1 - 2));
        self.branch_index = self
            .line
            .iter()
            .map(|v| v.iter().map(|_| None).collect::<Vec<_>>())
            .collect::<Vec<_>>();
        for (i, (y, x)) in self.branch_positions.iter().enumerate() {
            self.branch_index[*y][*x] = Some(i);
        }
        Self::parsed()
    }
    fn serialize(&self) -> Option<String> {
        #[derive(Debug, Default, Eq, PartialEq, Serialize)]
        struct Dump {
            map: Vec<Vec<u8>>,
            route: Vec<usize>,
        }
        let mut map: Vec<Vec<u8>> = self
            .line
            .clone()
            .iter()
            .map(|l| l.iter().map(|c| (*c == b'#') as u8).collect::<Vec<_>>())
            .collect::<Vec<_>>();
        for b in self.branch_positions.iter() {
            map[b.0][b.1] = 2;
        }
        let route = self.solution.clone().map_or(Vec::new(), |l| l.used);
        serde_json::to_string(&Dump { map, route }).ok()
    }
    fn part1(&mut self) -> Self::Output1 {
        let (height, width) = self.size;
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
        self.build_path_graph();
        let goal = self.branch_positions.len() - 1;
        let mut longest = 0;
        let mut longest_so_far = 0;
        let mut start = Route::default();
        start.used.push(0);
        let mut to_visit: Vec<Route> = Vec::new();
        let mut next: Vec<Route> = Vec::new();
        to_visit.push(start);
        while !to_visit.is_empty() {
            for p in to_visit.iter() {
                if p.pos == goal {
                    if longest < p.cost {
                        longest = p.cost;
                        progress!(longest);
                        self.solution = Some(p.clone());
                    }
                    continue;
                }
                for j in 1..self.branch_graph.len() {
                    if self.branch_graph[p.pos][j] < usize::MAX && !p.used.contains(&j) {
                        let mut q = p.clone();
                        q.pos = j;
                        q.cost = p.cost + self.branch_graph[p.pos][j];
                        longest_so_far = longest_so_far.max(q.cost);
                        q.used.push(j);
                        next.push(q);
                    }
                }
            }
            to_visit.clear();
            std::mem::swap(&mut to_visit, &mut next);
        }
        progress!("");
        self.dump();
        longest
    }
}

impl Puzzle {
    fn build_path_graph(&mut self) {
        self.branch_graph = (0..self.branch_positions.len())
            .map(|i| self.branch_distances(self.branch_positions[i]))
            .collect::<Vec<_>>();
    }
    fn branch_distances(&self, pos: Dim2<usize>) -> Vec<usize> {
        let size = self.size;
        let mut to_visit: BinaryHeap<Reverse<(usize, Dim2<usize>)>> = BinaryHeap::new();
        let mut visited: HashMap<Dim2<usize>, usize> = HashMap::new();
        to_visit.push(Reverse((0, pos)));
        while let Some(Reverse((cost, p))) = to_visit.pop() {
            if let Entry::Vacant(e) = visited.entry(p) {
                e.insert(cost);
                if p != pos && self.branch_index[p.0][p.1].is_some() {
                    continue;
                }
                for q in p.neighbors4((0, 0), size) {
                    if self.line[q.0][q.1] != b'#' && !visited.contains_key(&q) {
                        to_visit.push(Reverse((cost + 1, q)));
                    }
                }
            }
        }
        self.branch_positions
            .iter()
            .map(|pos| *visited.get(pos).unwrap_or(&usize::MAX))
            .collect::<Vec<_>>()
    }
    fn branch_map(&self) -> Vec<Vec<usize>> {
        let size = self.size;
        self.line
            .iter()
            .enumerate()
            .map(|(y, l)| {
                l.iter()
                    .enumerate()
                    .map(|(x, p)| {
                        (y, x)
                            .neighbors4((0, 0), size)
                            .into_iter()
                            .filter(|_| *p != b'#')
                            .filter(|(y, x)| self.line[*y][*x] != b'#')
                            .count()
                    })
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>()
    }
}
