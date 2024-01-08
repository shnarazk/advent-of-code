//! <https://adventofcode.com/2022/day/16>
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        progress, regex,
    },
    std::{
        cmp::Reverse,
        collections::{hash_map::Entry, BinaryHeap, HashMap, HashSet},
    },
};

#[derive(Debug, Default, Eq, PartialEq)]
pub struct Puzzle {
    line: Vec<(String, usize, Vec<String>)>,
    map: HashMap<usize, (usize, Vec<usize>)>,
    distance: HashMap<(usize, usize), usize>,
    label_id: HashMap<String, usize>,
}

#[aoc(2022, 16)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        let parser =
            regex!(r"^Valve (\w+) has flow rate=(\d+); tunnels? leads? to valves? ((\w+, )*\w+)$");
        let segment = parser.captures(block).ok_or(ParseError)?;
        self.line.push((
            segment[1].to_string(),
            segment[2].parse::<usize>()?,
            segment[3]
                .split(", ")
                .map(|s| s.to_string())
                .collect::<Vec<_>>(),
        ));
        Ok(())
    }
    fn end_of_data(&mut self) {
        let mut id = 0;
        for (label, _flow, linked) in self.line.iter() {
            if let Entry::Vacant(e) = self.label_id.entry(label.clone()) {
                e.insert(id);
                id += 1;
            }
            for dest in linked.iter() {
                if let Entry::Vacant(e) = self.label_id.entry(dest.clone()) {
                    e.insert(id);
                    id += 1;
                }
            }
        }
        for (label, flow, linked) in self.line.iter() {
            self.map.insert(
                *self.label_id.get(label).unwrap(),
                (
                    *flow,
                    linked
                        .iter()
                        .map(|l| *self.label_id.get(l).unwrap())
                        .collect::<Vec<_>>(),
                ),
            );
        }

        self.initialize_distances();
    }
    fn part1(&mut self) -> Self::Output1 {
        let aa = *self.label_id.get("AA").unwrap();
        let init = State {
            path: vec![aa],
            // contribution: vec![(0, 0)],
            ..Default::default()
        };
        self.traverse(init)
    }
    fn part2(&mut self) -> Self::Output2 {
        let aa = *self.label_id.get("AA").unwrap();
        let init = State2 {
            path: vec![aa],
            state1: (0, aa),
            state2: (0, aa),
            ..Default::default()
        };
        let mut best: usize = 0;
        let path_len = 1 + self.map.values().filter(|(f, _)| 0 < *f).count();
        self.traverse2(init, &mut best, path_len);
        best
    }
}

#[derive(Debug, Default, Eq, PartialEq)]
struct State {
    path: Vec<usize>,
    time: usize,
    total_flow: usize,
    // contribution: Vec<(usize, usize)>,
}

#[derive(Clone, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
struct State2 {
    total_flow: usize,
    path: Vec<usize>,
    state1: (usize, usize),
    state2: (usize, usize),
}

impl Puzzle {
    fn initialize_distances(&mut self) {
        for i in 0..self.label_id.len() {
            self.initialize_distances_from(i);
        }
    }
    fn initialize_distances_from(&mut self, label: usize) {
        #[derive(Debug, Eq, Ord, PartialEq, PartialOrd)]
        struct State {
            time: usize,
            loc: usize,
        }
        self.distance.insert((label, label), 0);
        let mut to_visit = BinaryHeap::new();
        to_visit.push(Reverse(State {
            time: 0,
            loc: label,
        }));
        let mut visited: HashSet<usize> = HashSet::new();
        visited.insert(label);
        while let Some(Reverse(state)) = to_visit.pop() {
            for next in self.map.get(&state.loc).unwrap().1.iter() {
                let key = (label, *next);
                if let std::collections::hash_map::Entry::Vacant(e) = self.distance.entry(key) {
                    e.insert(state.time + 1);
                    to_visit.push(Reverse(State {
                        loc: *next,
                        time: state.time + 1,
                    }));
                }
            }
        }
    }
    fn traverse(&self, state: State) -> usize {
        const REMAIN: usize = 30;
        if state.time == REMAIN {
            return state.total_flow;
        }
        let mut best = state.total_flow;
        let now = state.path.last().unwrap();
        for ((_, next), dist) in self.distance.iter().filter(|((s, _), _)| s == now) {
            if state.path.contains(next) {
                continue;
            }
            let time = state.time + *dist + 1;
            if REMAIN <= time {
                continue;
            }
            let flow = self.map.get(next).unwrap().0;
            if flow == 0 {
                continue;
            }
            let total_flow = state.total_flow + (REMAIN - time) * flow;
            let mut path = state.path.clone();
            path.push(*next);
            // let mut contribution = state.contribution.clone();
            // contribution.push((time, self.map.get(next).unwrap().0));
            best = self
                .traverse(State {
                    path,
                    time,
                    total_flow,
                    // contribution,
                })
                .max(best);
        }
        best
    }
    // calculate the expected reward in a cheap way
    fn reward_bound(&self, remain: usize, path: &[usize]) -> usize {
        self.map
            .iter()
            .filter(|(l, _)| !path.contains(l))
            .map(|(_, (f, _))| *f * remain)
            .sum()
    }
    fn traverse2(&self, state: State2, best: &mut usize, path_len: usize) {
        const DURATION: usize = 26;
        if *best < state.total_flow {
            *best = state.total_flow;
            progress!(*best);
        }
        if DURATION <= state.state1.0.min(state.state2.0) || state.path.len() == path_len {
            return;
        }
        let current = &(&state.state1).min(&state.state2).1;
        for ((_, label), dist) in self.distance.iter().filter(|((s, _), _)| s == current) {
            if state.path.contains(label) {
                continue;
            }
            let mut next = state.clone();
            let working = (&mut next.state1).min(&mut next.state2);
            working.0 += *dist + 1;
            working.1 = *label;
            let flow = self.map.get(label).unwrap().0;
            if DURATION <= working.0 || flow == 0 {
                continue;
            }
            next.total_flow += (DURATION - working.0) * flow;
            next.path.push(*label);
            if next.total_flow
                + self.reward_bound(DURATION - next.state1.0.max(next.state2.0) - 1, &next.path)
                < *best
            {
                continue;
            }
            self.traverse2(next, best, path_len);
        }
    }
}
