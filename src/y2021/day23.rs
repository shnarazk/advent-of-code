//! <https://adventofcode.com/2021/day/23>
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        progress,
    },
    std::{
        cmp::Reverse,
        collections::{BinaryHeap, HashSet},
    },
};

#[derive(Clone, Debug, Default)]
pub struct Puzzle {
    line: Vec<char>,
}

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialOrd, PartialEq)]
struct P1 {
    cost: usize,
    state: [char; 7],
    rooms: [Vec<char>; 4],
}

impl P1 {
    fn heuristics(&self) -> isize {
        self.rooms
            .iter()
            .enumerate()
            .map(|(i, r)| {
                let target = (b'A' + i as u8) as char;
                let point = 10isize.pow(i as u32);
                match (r[0], r[1]) {
                    (r0, r1) if r0 == target && r1 == target => 11 * point,
                    ('.', r1) if r1 == target => 10 * point,
                    (_, r1) if r1 == target => 9 * point,
                    ('.', '.') => 0,
                    ('.', _) => -10 * point,
                    (_, _) => -11 * point,
                }
            })
            .sum()
    }
    fn walkable_between(&self, s: usize, room_number: usize, maybe_me: Option<char>) -> bool {
        if s < room_number + 2 {
            (s..room_number + 2).all(|i| {
                self.state[i] == '.' || maybe_me.map_or(false, |me| i == s && self.state[i] == me)
            })
        } else {
            (room_number + 2..=s).all(|i| {
                self.state[i] == '.' || maybe_me.map_or(false, |me| i == s && self.state[i] == me)
            })
        }
    }
    fn neighbor_states(&self) -> Vec<Self> {
        const COST: [usize; 4] = [1, 10, 100, 1000];
        let mut result: Vec<Self> = Vec::new();
        // move out from a room
        for (i, r) in self.rooms.iter().enumerate() {
            let satisfied = (b'A' + i as u8) as char;
            for (d, amph) in r.iter().enumerate() {
                if r.iter().take(d).any(|c| *c != '.')
                    || *amph == '.'
                    || r.iter().skip(d).all(|x| *x == satisfied)
                {
                    continue;
                }
                for (j, v) in self.state.iter().enumerate() {
                    if !self.walkable_between(j, i, None) {
                        continue;
                    }
                    let mut news = (*self).clone();
                    debug_assert_eq!(*v, '.');
                    news.state[j] = *amph;
                    news.rooms[i][d] = '.';
                    news.cost += COST[(*amph as u8 - b'A') as usize] * (DIST_FROM_ROOM[i][j] + d);
                    result.push(news);
                }
            }
        }
        // move in to a room
        for (i, amph) in self.state.iter().enumerate() {
            if *amph == '.' {
                continue;
            }
            for (j, r) in self.rooms.iter().enumerate() {
                let satisfied = (b'A' + j as u8) as char;
                if *amph != satisfied {
                    continue;
                }
                for d in 0..r.len() {
                    if r.iter().take(d + 1).any(|x| *x != '.')
                        || r.iter().skip(d + 1).any(|x| *x != satisfied)
                        || !self.walkable_between(i, j, Some(*amph))
                    {
                        continue;
                    }
                    let mut news = (*self).clone();
                    news.state[i] = '.';
                    debug_assert_eq!(news.rooms[j][d], '.');
                    news.rooms[j][d] = *amph;
                    news.cost += COST[(*amph as u8 - b'A') as usize] * (DIST_FROM_ROOM[j][i] + d);
                    result.push(news);
                }
            }
        }
        result
    }
}

const DIST_FROM_ROOM: [[usize; 7]; 4] = [
    [3, 2, 2, 4, 6, 8, 9],
    [5, 4, 2, 2, 4, 6, 7],
    [7, 6, 4, 2, 2, 4, 5],
    [9, 8, 6, 4, 2, 2, 3],
];

#[aoc(2021, 23)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.line
            .append(&mut block.trim().chars().collect::<Vec<char>>());
        Ok(())
    }
    fn end_of_data(&mut self) {
        self.line.retain(|c| *c != '#' && *c != '.');
    }
    fn part1(&mut self) -> Self::Output1 {
        let goal: P1 = P1 {
            cost: 0,
            state: ['.', '.', '.', '.', '.', '.', '.'],
            rooms: [
                vec!['A', 'A'],
                vec!['B', 'B'],
                vec!['C', 'C'],
                vec!['D', 'D'],
            ],
        };
        let start = P1 {
            cost: 0,
            state: goal.state,
            rooms: [
                vec![self.line[0], self.line[4]],
                vec![self.line[1], self.line[5]],
                vec![self.line[2], self.line[6]],
                vec![self.line[3], self.line[7]],
            ],
        };
        self.search(start, goal)
    }
    fn part2(&mut self) -> Self::Output2 {
        let goal: P1 = P1 {
            cost: 0,
            state: ['.', '.', '.', '.', '.', '.', '.'],
            rooms: [
                vec!['A', 'A', 'A', 'A'],
                vec!['B', 'B', 'B', 'B'],
                vec!['C', 'C', 'C', 'C'],
                vec!['D', 'D', 'D', 'D'],
            ],
        };
        let start = P1 {
            cost: 0,
            state: goal.state,
            rooms: [
                vec![self.line[0], 'D', 'D', self.line[4]],
                vec![self.line[1], 'C', 'B', self.line[5]],
                vec![self.line[2], 'B', 'A', self.line[6]],
                vec![self.line[3], 'A', 'C', self.line[7]],
            ],
        };
        self.search(start, goal)
    }
}

impl Puzzle {
    fn search(&self, start: P1, goal: P1) -> usize {
        let mut point: isize = start.heuristics();
        let mut to_visit: BinaryHeap<Reverse<P1>> = BinaryHeap::new();
        to_visit.push(Reverse(start));
        let mut visited: HashSet<P1> = HashSet::new();
        while let Some(Reverse(state)) = to_visit.pop() {
            if visited.contains(&state) {
                continue;
            }
            if state.state == goal.state && state.rooms == goal.rooms {
                progress!("");
                return state.cost;
            }
            let h = state.heuristics();
            if point < h {
                point = h;
                progress!(format!(
                    "{:>6}({:>6}), {:?} {:?}, {:>8}",
                    state.cost,
                    point,
                    state.state.iter().collect::<String>(),
                    state
                        .rooms
                        .iter()
                        .map(|r| r.iter().collect::<String>())
                        .collect::<Vec<_>>(),
                    visited.len(),
                ));
            }
            for news in state.neighbor_states() {
                to_visit.push(Reverse(news));
            }
            visited.insert(state);
        }
        unreachable!()
    }
}
