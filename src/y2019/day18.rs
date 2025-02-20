//! <https://adventofcode.com/2019/day/18>
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::neighbors4,
        progress,
    },
    std::{
        cmp::Reverse,
        collections::{BinaryHeap, HashMap, HashSet, VecDeque},
    },
};

const ENTRANCE: u8 = b'@';
const OPEN: u8 = b'.';
const WALL: u8 = b'#';

type Location = (usize, usize);

///
/// For part 1
///
#[derive(Clone, Debug, Default, Eq, PartialEq, Ord, PartialOrd, Hash)]
struct State {
    estimate: usize,
    current_cost: usize,
    inventry: Vec<u8>,
}

///
/// For part 2
///
#[derive(Clone, Debug, Default, Eq, PartialEq, Ord, PartialOrd, Hash)]
struct State4 {
    estimate: usize,
    current_cost: usize,
    inventry: [Vec<u8>; 4],
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Puzzle {
    line: Vec<Vec<u8>>,
    map: HashMap<Location, u8>,
    location: HashMap<u8, Location>,
    height: usize,
    width: usize,
    keys: Vec<u8>,
}

#[aoc(2019, 18)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn parse_block(&mut self, block: &str) -> Result<(), ParseError> {
        self.line
            .push(block.chars().map(|c| c as u8).collect::<Vec<u8>>());
        Ok(())
    }
    fn end_of_data(&mut self) {
        for (j, v) in self.line.iter().enumerate() {
            for (i, c) in v.iter().enumerate() {
                self.map.insert((j, i), *c);
                if ![OPEN, WALL].contains(c) {
                    self.location.insert(*c, (j, i));
                }
            }
        }
        self.height = self.line.len();
        self.width = self.line[0].len();
        self.keys = self
            .map
            .values()
            .filter(|c| b'a' <= **c && **c <= b'z')
            .copied()
            .collect::<Vec<u8>>();
    }
    fn part1(&mut self) -> Self::Output1 {
        let n_keys = self.keys.len();
        let shortest = 5;
        let mut to_check: BinaryHeap<Reverse<State>> = BinaryHeap::new();
        let mut visited: HashSet<State> = HashSet::new();
        to_check.push(Reverse(State {
            estimate: n_keys * shortest,
            current_cost: 0,
            inventry: vec![],
        }));
        let mut len = 0;
        while let Some(Reverse(state)) = to_check.pop() {
            if 4545 <= state.current_cost {
                continue;
            }
            if visited.contains(&state) {
                continue;
            }
            if state.inventry.len() == self.keys.len() {
                return state.current_cost;
            }
            if len < state.inventry.len() {
                len = state.inventry.len();
                progress!(format!("{}:{}/{}", len, state.estimate, to_check.len()));
            }
            let from = *state.inventry.last().unwrap_or(&ENTRANCE);
            let map = self.build_cost_map(from, &state.inventry);
            for to in self.keys.iter().filter(|k| !state.inventry.contains(k)) {
                if let Some(c) = map.get(to) {
                    let mut inv = state.inventry.clone();
                    inv.sort();
                    inv.push(*to);
                    let e: usize = state.current_cost + c + (n_keys - inv.len()) * shortest;
                    if !to_check
                        .iter()
                        .any(|Reverse(s)| inv == s.inventry && s.estimate < e)
                    {
                        to_check.push(Reverse(State {
                            estimate: e,
                            current_cost: state.current_cost + c,
                            inventry: inv,
                        }));
                    }
                }
            }
            visited.insert(state);
        }
        0
    }
    fn part2(&mut self) -> Self::Output2 {
        {
            let orig_ent = *self.location.get(&ENTRANCE).unwrap();
            let mut ent: u8 = b'0';
            for j in -1_isize..=1 {
                for i in -1_isize..=1 {
                    let loc = (
                        (orig_ent.0 as isize + j) as usize,
                        (orig_ent.1 as isize + i) as usize,
                    );
                    let is_ent = (j * i).abs() == 1;
                    self.map.insert(loc, if is_ent { ent } else { WALL });
                    if is_ent {
                        self.location.insert(ent, loc);
                        ent += 1;
                    }
                }
            }
        }
        let n_keys = self.keys.len();
        let shortest = 80;
        let mut to_check: BinaryHeap<Reverse<State4>> = BinaryHeap::new();
        let mut visited: HashSet<State4> = HashSet::new();
        to_check.push(Reverse(State4 {
            estimate: n_keys * shortest,
            current_cost: 0,
            inventry: [vec![], vec![], vec![], vec![]],
        }));
        let mut len = 0;
        while let Some(Reverse(state)) = to_check.pop() {
            if 1693 <= state.current_cost {
                continue;
            }
            if visited.contains(&state) {
                continue;
            }
            let len_inventry = state.inventry.iter().map(|v| v.len()).sum::<usize>();
            {
                if len_inventry == n_keys {
                    progress!("");
                    return state.current_cost;
                }
                if len < len_inventry {
                    len = len_inventry;
                    progress!(format!(
                        "got {}: estimated cost={}, states={}",
                        len,
                        state.estimate,
                        to_check.len()
                    ));
                }
            }
            for i in 0..4 {
                let from = *state.inventry[i].last().unwrap_or(&(b'0' + i as u8));
                let map = self.build_cost_map2(from, &state.inventry);
                for to in self.keys.iter().filter(|k| {
                    !state.inventry[0].contains(k)
                        && !state.inventry[1].contains(k)
                        && !state.inventry[2].contains(k)
                        && !state.inventry[3].contains(k)
                }) {
                    if let Some(c) = map.get(to) {
                        let mut inv = state.inventry.clone();
                        inv[i].sort();
                        inv[i].push(*to);
                        let n_inv = len_inventry + 1;
                        let e: usize = state.current_cost + c + (n_keys - n_inv) * shortest;
                        if !to_check
                            .iter()
                            .any(|Reverse(s)| inv == s.inventry && s.estimate < e)
                        {
                            to_check.push(Reverse(State4 {
                                estimate: e,
                                current_cost: state.current_cost + c,
                                inventry: inv,
                            }));
                        }
                    }
                }
            }
            visited.insert(state);
        }
        0
    }
}

impl Puzzle {
    fn build_cost_map(&self, from: u8, inventry: &[u8]) -> HashMap<u8, usize> {
        let mut cost: HashMap<Location, usize> = HashMap::new();
        let mut result: HashMap<u8, usize> = HashMap::new();
        let mut to_visit: VecDeque<Location> = VecDeque::new();
        let start = *self.location.get(&from).unwrap();
        to_visit.push_back(start);
        cost.insert(start, 0);
        while let Some(loc) = to_visit.pop_front() {
            let c = *cost.get(&loc).unwrap();
            for l in neighbors4(loc.0, loc.1, self.height, self.width).iter() {
                if self.map.get(l).map_or_else(
                    || false,
                    |k| {
                        [ENTRANCE, OPEN].contains(k)
                            || (b'a' <= *k && *k <= b'z')
                            || (b'A' <= *k && *k <= b'Z' && inventry.contains(&(*k + b'a' - b'A')))
                    },
                ) && !cost.contains_key(l)
                {
                    cost.insert(*l, c + 1);
                    let k = self.map.get(l).unwrap();
                    if ![OPEN, ENTRANCE].contains(k) {
                        result.insert(*k, c + 1);
                    }
                    // if we can get a new key, there's no reason to skip it and go further.
                    if b'a' <= *k && *k <= b'z' && !inventry.contains(k) {
                        continue;
                    }
                    to_visit.push_back(*l);
                }
            }
        }
        result
    }
    fn build_cost_map2(&self, from: u8, inventry: &[Vec<u8>; 4]) -> HashMap<u8, usize> {
        let mut cost: HashMap<Location, usize> = HashMap::new();
        let mut result: HashMap<u8, usize> = HashMap::new();
        let mut to_visit: VecDeque<Location> = VecDeque::new();
        let start = *self.location.get(&from).unwrap();
        to_visit.push_back(start);
        cost.insert(start, 0);
        while let Some(loc) = to_visit.pop_front() {
            let c = *cost.get(&loc).unwrap();
            for l in neighbors4(loc.0, loc.1, self.height, self.width).iter() {
                if self.map.get(l).map_or_else(
                    || false,
                    |k| {
                        [b'0', b'1', b'2', b'3', OPEN].contains(k)
                            || (b'a' <= *k && *k <= b'z')
                            || (b'A' <= *k
                                && *k <= b'Z'
                                && inventry.iter().any(|v| v.contains(&(*k + b'a' - b'A'))))
                    },
                ) && !cost.contains_key(l)
                {
                    cost.insert(*l, c + 1);
                    let k = self.map.get(l).unwrap();
                    if ![OPEN, b'0', b'1', b'2', b'3'].contains(k) {
                        result.insert(*k, c + 1);
                    }
                    // if we can get a new key, there's no reason to skip it and go further.
                    if b'a' <= *k && *k <= b'z' && inventry.iter().all(|v| !v.contains(k)) {
                        continue;
                    }
                    to_visit.push_back(*l);
                }
            }
        }
        result
    }
}
