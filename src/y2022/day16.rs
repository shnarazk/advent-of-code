//! <https://adventofcode.com/2022/day/16>
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        regex,
    },
    std::{
        cmp::Reverse,
        collections::{BinaryHeap, HashMap, HashSet},
    },
};

#[derive(Debug, Default, Eq, PartialEq)]
pub struct Puzzle {
    line: Vec<(String, usize, Vec<String>)>,
    map: HashMap<String, (usize, Vec<String>)>,
    distance: HashMap<(String, String), usize>,
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
    fn after_insert(&mut self) {
        for (label, flow, linked) in self.line.iter() {
            self.map.insert(label.clone(), (*flow, linked.clone()));
        }
        self.initialize_distacnes();
        dbg!(&self.distance.len());
    }
    fn part1(&mut self) -> Self::Output1 {
        let init = State {
            path: vec!["AA".to_string()],
            // contribution: vec![(0, 0)],
            ..Default::default()
        };
        self.traverse(init)
    }
    fn part2(&mut self) -> Self::Output2 {
        let init = State2 {
            path: vec!["AA".to_string()],
            state1: (0, "AA".to_string()),
            state2: (0, "AA".to_string()),
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
    path: Vec<String>,
    time: usize,
    total_flow: usize,
    // contribution: Vec<(usize, usize)>,
}

#[derive(Clone, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
struct State2 {
    total_flow: usize,
    path: Vec<String>,
    state1: (usize, String),
    state2: (usize, String),
}

impl Puzzle {
    fn initialize_distacnes(&mut self) {
        let labels = self.map.keys().cloned().collect::<Vec<_>>();
        for l in labels.iter() {
            self.initialize_distances_from(l.to_string());
        }
    }
    fn initialize_distances_from(&mut self, label: String) {
        #[derive(Debug, Eq, Ord, PartialEq, PartialOrd)]
        struct State<'a> {
            time: usize,
            loc: &'a String,
        }
        self.distance.insert((label.clone(), label.clone()), 0);
        let mut to_visit = BinaryHeap::new();
        to_visit.push(Reverse(State {
            loc: &label,
            time: 0,
        }));
        let mut visited: HashSet<&String> = HashSet::new();
        visited.insert(&label);
        while let Some(Reverse(state)) = to_visit.pop() {
            for next in self.map.get(state.loc).unwrap().1.iter() {
                let key = (label.clone(), next.clone());
                if let std::collections::hash_map::Entry::Vacant(e) = self.distance.entry(key) {
                    e.insert(state.time + 1);
                    to_visit.push(Reverse(State {
                        loc: next,
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
            path.push(next.clone());
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
    fn reward_bound(&self, remain: usize, path: &[String]) -> usize {
        self.map
            .iter()
            .filter(|(l, _)| !path.contains(l))
            .map(|(_, (f, _))| *f * remain)
            .sum()
    }
    fn traverse2(&self, state: State2, best: &mut usize, path_len: usize) {
        const DURATION: usize = 26;
        if *best < state.total_flow {
            *best = dbg!(state.total_flow);
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
            working.1 = label.clone();
            let flow = self.map.get(label).unwrap().0;
            if DURATION <= working.0 || flow == 0 {
                continue;
            }
            next.total_flow += (DURATION - working.0) * flow;
            next.path.push(label.clone());
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
