//! <https://adventofcode.com/2022/day/16>
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        parser::parse_usize,
        progress,
    },
    std::{
        cmp::Reverse,
        collections::{hash_map::Entry, BinaryHeap, HashMap, HashSet},
    },
    winnow::{
        ascii::newline,
        combinator::{alt, separated, seq},
        token::one_of,
        PResult, Parser,
    },
};

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Puzzle {
    line: Vec<(String, usize, Vec<String>)>,
    map: HashMap<usize, (usize, Vec<usize>)>,
    distance: HashMap<(usize, usize), usize>,
    label_id: HashMap<String, usize>,
}

fn parse_name(s: &mut &str) -> PResult<String> {
    (one_of('A'..='Z'), one_of('A'..='Z'))
        .map(|(c1, c2)| format!("{c1}{c2}"))
        .parse_next(s)
}

fn parse_line(s: &mut &str) -> PResult<(String, usize, Vec<String>)> {
    seq!(
        _: "Valve ", parse_name,
        _: " has flow rate=", parse_usize,
        _: alt(("; tunnel leads to ", "; tunnels lead to ")),
        _: alt(("valve ", "valves ")),
        separated::<_, String, Vec<String>, _, _, _, _>(1.., parse_name, ", ")
    )
    .map(|(name, num, vec)| (name, num, vec))
    .parse_next(s)
}

fn parse(s: &mut &str) -> PResult<Vec<(String, usize, Vec<String>)>> {
    separated(1.., parse_line, newline).parse_next(s)
}

#[aoc(2022, 16)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, input: String) -> Result<String, ParseError> {
        self.line = parse(&mut input.as_str())?;
        Self::parsed()
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
        let mut used = vec![false; self.label_id.len()];
        used[aa] = true;
        let init = State {
            used,
            last: aa,
            ..Default::default()
        };
        self.traverse(init)
    }
    fn part2(&mut self) -> Self::Output2 {
        let aa = *self.label_id.get("AA").unwrap();
        let mut used = vec![false; self.label_id.len()];
        used[aa] = true;
        let init = State2 {
            used,
            state1: (0, aa),
            state2: (0, aa),
            ..Default::default()
        };
        // let path_len = 1 + self.map.values().filter(|(f, _)| 0 < *f).count();
        self.traverse2(init)
    }
}

#[derive(Clone, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
struct State {
    estimate: usize,
    total_flow: usize,
    used: Vec<bool>,
    last: usize,
    time: usize,
}

#[derive(Clone, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
struct State2 {
    estimate: usize,
    total_flow: usize,
    used: Vec<bool>,
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
    // calculate the expected reward in a cheap way
    fn reward_bound(&self, remain: usize, path: &[bool]) -> usize {
        self.map
            .iter()
            .filter(|(l, _)| !path[**l])
            .map(|(_, (f, _))| *f * remain)
            .sum()
    }
    fn traverse(&self, state: State) -> usize {
        let mut best = 0;
        let mut to_visit: BinaryHeap<State> = BinaryHeap::new();
        to_visit.push(state);
        let mut visited: HashMap<(usize, Vec<bool>), usize> = HashMap::new();
        const DURATION: usize = 30;
        while let Some(state) = to_visit.pop() {
            let current_pos = state.last;
            if DURATION < state.time {
                continue;
            }
            if best < state.total_flow {
                best = state.total_flow;
                progress!(best);
            }
            if visited
                .get(&(state.time, state.used.clone()))
                .is_some_and(|v| state.total_flow < *v)
            {
                continue;
            }
            for ((s, dist), travel_time) in self.distance.iter() {
                if *s != current_pos || state.used[*dist] {
                    continue;
                }
                let flow = self.map.get(dist).unwrap().0;
                let time = state.time + *travel_time + 1;
                if DURATION <= time || flow == 0 {
                    continue;
                }
                let mut next = state.clone();
                next.time = time;
                next.last = *dist;
                next.total_flow += (DURATION - next.time) * flow;
                next.used[*dist] = true;
                let estimate =
                    next.total_flow + self.reward_bound(DURATION - next.time - 1, &next.used);
                if estimate < best {
                    continue;
                }
                next.estimate = estimate;
                to_visit.push(next)
            }
            visited.insert((state.time, state.used), state.total_flow);
        }
        best
    }
    fn traverse2(&self, state: State2) -> usize {
        let mut best = 0;
        let mut to_visit: BinaryHeap<State2> = BinaryHeap::new();
        to_visit.push(state);
        let mut visited: HashMap<(usize, Vec<bool>), usize> = HashMap::new();
        const DURATION: usize = 26;
        while let Some(state) = to_visit.pop() {
            if best < state.total_flow {
                best = state.total_flow;
                progress!(best);
            }
            let pos = (&state.state1).min(&state.state2).1;
            let now = (&state.state1).max(&state.state2).0;
            if DURATION <= state.state1.0.min(state.state2.0) {
                continue;
            }
            if visited
                .get(&(now, state.used.clone()))
                .is_some_and(|v| state.total_flow < *v)
            {
                continue;
            }
            for ((s, dist), travel_time) in self.distance.iter() {
                if *s != pos || state.used[*dist] {
                    continue;
                }
                let mut next = state.clone();
                let working = (&mut next.state1).min(&mut next.state2);
                working.0 += *travel_time + 1;
                working.1 = *dist;
                let flow = self.map.get(dist).unwrap().0;
                if DURATION <= working.0 || flow == 0 {
                    continue;
                }
                next.total_flow += (DURATION - working.0) * flow;
                next.used[*dist] = true;
                let estimate = next.total_flow
                    + self
                        .reward_bound(DURATION - next.state1.0.max(next.state2.0) - 1, &next.used);
                if estimate < best {
                    continue;
                }
                next.estimate = estimate;
                to_visit.push(next)
            }
            visited.insert((now, state.used), state.total_flow);
        }
        best
    }
}
