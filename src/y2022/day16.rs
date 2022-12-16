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
            contribution: vec![(0, 0)],
            ..Default::default()
        };
        self.traverse(init)
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut bound: HashMap<String, usize> = HashMap::new();
        let init = State2 {
            path: vec!["AA".to_string()],
            pos1: "AA".to_string(),
            pos2: "AA".to_string(),
            ..Default::default()
        };
        self.traverse2_1(init, &mut bound)
    }
}

#[derive(Debug, Default, Eq, PartialEq)]
struct State {
    path: Vec<String>,
    time: usize,
    total_flow: usize,
    contribution: Vec<(usize, usize)>,
}

#[derive(Debug, Default, Eq, PartialEq)]
struct State2 {
    path: Vec<String>,
    pos1: String,
    time1: usize,
    pos2: String,
    time2: usize,
    total_flow: usize,
    contribution: Vec<(usize, usize)>,
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
            let mut contribution = state.contribution.clone();
            contribution.push((time, self.map.get(next).unwrap().0));
            best = self
                .traverse(State {
                    path,
                    time,
                    total_flow,
                    contribution,
                })
                .max(best);
        }
        best
    }
    fn traverse2_1(&self, state: State2, bound: &mut HashMap<String, usize>) -> usize {
        const REMAIN: usize = 26;
        if state.time1 == REMAIN {
            return state.total_flow;
        }
        let mut best = state.total_flow;
        let now = state.pos1;
        for ((_, next), dist) in self.distance.iter().filter(|((s, _), _)| *s == now) {
            if state.path.contains(next) {
                continue;
            }
            let time1 = state.time1 + *dist + 1;
            if REMAIN <= time1 {
                continue;
            }
            let flow = self.map.get(next).unwrap().0;
            if flow == 0 {
                continue;
            }
            let total_flow = state.total_flow + (REMAIN - time1) * flow;
            let mut path = state.path.clone();
            path.push(next.clone());
            {
                // Let's prune bad branches!
                let mut tmp = path.clone();
                tmp.sort();
                let key = tmp.join("");
                let e = bound.entry(key).or_insert(0);
                if total_flow < *e {
                    continue;
                }
                *e = total_flow;
            }
            let mut contribution = state.contribution.clone();
            contribution.push((time1, self.map.get(next).unwrap().0));
            best = if time1 < state.time2 {
                self.traverse2_1(
                    State2 {
                        path,
                        pos1: next.to_string(),
                        time1,
                        pos2: state.pos2.clone(),
                        time2: state.time2,
                        total_flow,
                        contribution,
                    },
                    bound,
                )
                .max(best)
            } else {
                self.traverse2_2(
                    State2 {
                        path,
                        pos1: next.to_string(),
                        time1,
                        pos2: state.pos2.clone(),
                        time2: state.time2,
                        total_flow,
                        contribution,
                    },
                    bound,
                )
                .max(best)
            }
        }
        best
    }
    fn traverse2_2(&self, state: State2, bound: &mut HashMap<String, usize>) -> usize {
        const REMAIN: usize = 26;
        if state.time2 == REMAIN {
            return state.total_flow;
        }
        let mut best = state.total_flow;
        let now = state.pos2;
        for ((_, next), dist) in self.distance.iter().filter(|((s, _), _)| *s == now) {
            if state.path.contains(next) {
                continue;
            }
            let time2 = state.time2 + *dist + 1;
            if REMAIN <= time2 {
                continue;
            }
            let flow = self.map.get(next).unwrap().0;
            if flow == 0 {
                continue;
            }
            let total_flow = state.total_flow + (REMAIN - time2) * flow;
            let mut path = state.path.clone();
            path.push(next.clone());
            {
                let mut tmp = path.clone();
                tmp.sort();
                let key = tmp.join("");
                let e = bound.entry(key).or_insert(0);
                if total_flow < *e {
                    continue;
                }
                *e = total_flow;
            }
            let mut contribution = state.contribution.clone();
            contribution.push((time2, self.map.get(next).unwrap().0));
            best = if time2 < state.time1 {
                self.traverse2_2(
                    State2 {
                        path,
                        pos1: state.pos1.clone(),
                        time1: state.time1,
                        pos2: next.to_string(),
                        time2,
                        total_flow,
                        contribution,
                    },
                    bound,
                )
                .max(best)
            } else {
                self.traverse2_1(
                    State2 {
                        path,
                        pos1: state.pos1.clone(),
                        time1: state.time1,
                        pos2: next.to_string(),
                        time2,
                        total_flow,
                        contribution,
                    },
                    bound,
                )
                .max(best)
            }
        }
        best
    }
}
