//! <https://adventofcode.com/2016/day/11>

use {
    crate::framework::{AdventOfCode, aoc},
    std::collections::{BinaryHeap, HashSet},
};

#[derive(Debug)]
struct State<const N: usize = 15> {
    state: [u8; N],
    cost: usize,
    estimate: isize,
}

const FLOORS: usize = 4;

impl<const N: usize> Default for State<N> {
    fn default() -> Self {
        State {
            state: [0; N],
            cost: 0,
            estimate: 0,
        }
    }
}

impl<const N: usize> From<[u8; N]> for State<N> {
    fn from(v: [u8; N]) -> Self {
        State {
            state: v,
            ..Default::default()
        }
    }
}

impl<const N: usize> PartialEq for State<N> {
    fn eq(&self, other: &Self) -> bool {
        self.state.eq(&other.state)
    }
}
impl<const N: usize> Eq for State<N> {}
impl<const N: usize> PartialOrd for State<N> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl<const N: usize> Ord for State<N> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.estimate.cmp(&other.estimate)
    }
}

impl<const N: usize> State<N> {
    fn is_goal(&self) -> bool {
        self.state.iter().all(|s| *s == FLOORS as u8 - 1)
    }
    fn index(&self) -> usize {
        self.state
            .iter()
            .fold(0_usize, |sum, digit| *digit as usize + sum * 4)
    }
    fn kinds(&self) -> std::ops::Range<usize> {
        0..(N - 1) / 2
    }
    fn elevator(&self) -> u8 {
        self.state[0]
    }
    fn generator(&self, k: usize) -> u8 {
        self.state[2 * k + 1]
    }
    fn chip(&self, k: usize) -> u8 {
        self.state[2 * k + 2]
    }
    fn is_safe(&self) -> bool {
        for k in self.kinds() {
            if self.generator(k) == self.chip(k) {
                continue;
            }
            let ff = self.chip(k);
            if self.kinds().any(|kk| self.generator(kk) == ff) {
                return false;
            }
        }
        true
    }
    fn move_floor(&self, f: u8, i: usize, j: usize) -> Option<Self> {
        let mut v = self.state;
        v[0] = f;
        v[i] = f;
        v[j] = f;
        let e = self
            .kinds()
            .map(|k| 12 - (v[2 * k + 1] + 2 * v[2 * k + 2]) as usize)
            .sum::<usize>();
        let s = Self {
            state: v,
            cost: self.cost + 1,
            estimate: -(self.cost as isize + 1 + (e as isize)),
        };
        s.is_safe().then_some(s)
    }
    fn adjacent(&self) -> std::vec::IntoIter<State<N>> {
        let mut list: Vec<State<N>> = Vec::new();
        let floor = self.elevator();
        for i in 1..N {
            if floor != self.state[i] {
                continue;
            }
            for j in i..N {
                if floor != self.state[j] {
                    continue;
                }
                for f in [floor.checked_sub(1), floor.checked_add(1)]
                    .into_iter()
                    .flatten()
                {
                    if f < (FLOORS as u8)
                        && let Some(state) = self.move_floor(f, i, j)
                    {
                        list.push(state);
                    }
                }
            }
        }
        list.into_iter()
    }
}

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {}

#[aoc(2016, 11)]
impl AdventOfCode for Puzzle {
    fn part1(&mut self) -> Self::Output1 {
        // The 0 floor: a strontium G, a strontium M, a plutonium G, a plutonium M.
        // The 1 floor: a thulium G, a ruthenium G, a ruthenium M, a curium G, a curium M.
        // The 2 floor: a thulium M.
        // The 3 floor: nothing relevant.
        // let start: State<5> = State::from([0, 1, 0, 2, 0]);
        // let mut visit: HashSet<usize> = HashSet::new();
        // let mut bag: BinaryHeap<State<5>> = BinaryHeap::new();
        // bag.push(start);
        // while let Some(state) = bag.pop() {
        //     if state.is_goal() {
        //         return state.cost;
        //     }
        //     // dbg!(state.cost);
        //     visit.insert(state.index());
        //     for s in state.adjacent().filter(|s| !visit.contains(&s.index())) {
        //         bag.push(s);
        //     }
        //     if 1000 < bag.len() {
        //         dbg!(bag);
        //         dbg!(visit);
        //         return 0;
        //     }
        // }
        let mut visited: HashSet<usize> = HashSet::new();
        let mut bag: BinaryHeap<State<11>> = BinaryHeap::new();
        bag.push(State::from([0, 0, 0, 0, 0, 1, 2, 1, 1, 1, 1]));
        while let Some(state) = bag.pop() {
            if state.is_goal() {
                return state.cost;
            }
            let index = state.index();
            if visited.contains(&index) {
                continue;
            }
            visited.insert(index);
            for s in state.adjacent() {
                bag.push(s);
            }
        }
        0
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut visited: HashSet<usize> = HashSet::new();
        let mut bag: BinaryHeap<State<15>> = BinaryHeap::new();
        bag.push(State::from([0, 0, 0, 0, 0, 1, 2, 1, 1, 1, 1, 0, 0, 0, 0]));
        while let Some(state) = bag.pop() {
            if state.is_goal() {
                return state.cost;
            }
            let index = state.index();
            if visited.contains(&index) {
                continue;
            }
            visited.insert(index);
            for s in state.adjacent() {
                bag.push(s);
            }
        }
        0
    }
}
