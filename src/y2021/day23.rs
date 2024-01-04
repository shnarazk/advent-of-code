//! <https://adventofcode.com/2021/day/23>
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        line_parser,
    },
    std::cmp::{Ord, Ordering, PartialOrd},
};

#[derive(Debug, Default)]
pub struct Puzzle {
    line: Vec<char>,
}

#[derive(Clone, Debug, Default)]
struct P1 {
    // val: usize,
    id: usize,
    cost: usize,
    state: [char; 7],
    rooms: [Vec<char>; 4],
    pre: usize,
}

impl PartialOrd for P1 {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cost.cmp(&other.cost))
    }
}

impl Ord for P1 {
    fn cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(other).unwrap()
    }
}

impl PartialEq for P1 {
    fn eq(&self, to: &Self) -> bool {
        self.state == to.state && self.rooms == to.rooms
    }
}

impl Eq for P1 {}

trait Game {
    fn check_them(&self, msg: &str);
    fn walkable_between(&self, s: usize, r: usize, maybe_me: Option<char>) -> bool;
    fn neighbor_states(&self) -> Vec<Self>
    where
        Self: Sized;
    fn heuristics(&self) -> isize;
}

impl Game for P1 {
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
    fn check_them(&self, _msg: &str) {
        /*
                debug_assert!(
                    self.state.iter().filter(|c| **c != '.').count()
                        + self
                            .rooms
                            .iter()
                            .map(|r| r.iter().filter(|c| **c != '.').count())
                            .sum::<usize>()
                        == 8,
                    "!! {}",
                    msg
                );
        */
    }
    fn walkable_between(&self, s: usize, room_number: usize, maybe_me: Option<char>) -> bool {
        if s < room_number + 2 {
            (s..room_number + 2).all(|i| {
                self.state[i] == '.'
                    || maybe_me.map_or_else(|| false, |me| i == s && self.state[i] == me)
            })
        } else {
            (room_number + 2..=s).all(|i| {
                self.state[i] == '.'
                    || maybe_me.map_or_else(|| false, |me| i == s && self.state[i] == me)
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
                    // news.check_them("out");
                    news.pre = self.id;
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
                    news.pre = self.id;
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
        self.line.append(&mut line_parser::to_chars(block)?);
        Ok(())
    }
    fn end_of_data(&mut self) {
        self.line.retain(|c| *c != '#' && *c != '.');
        dbg!(&self.line.len());
    }
    fn part1(&mut self) -> Self::Output1 {
        let goal: P1 = P1 {
            id: 0,
            cost: 0,
            state: ['.', '.', '.', '.', '.', '.', '.'],
            rooms: [
                vec!['A', 'A'],
                vec!['B', 'B'],
                vec!['C', 'C'],
                vec!['D', 'D'],
            ],
            pre: 0,
        };
        let init = P1 {
            id: 0,
            cost: 0,
            state: goal.state,
            rooms: [
                vec![self.line[0], self.line[4]],
                vec![self.line[1], self.line[5]],
                vec![self.line[2], self.line[6]],
                vec![self.line[3], self.line[7]],
            ],
            pre: 0,
        };
        let mut point: isize = init.heuristics();
        let mut expanded: Vec<P1> = vec![init];
        let mut updated: Vec<P1> = expanded.clone();
        let mut id_counter = 0;
        while let Some(rstate) = updated.iter().min_by_key(|s| s.cost) {
            let state = rstate.clone();
            if state == goal {
                debug_assert!(updated.iter().min_by_key(|s| s.cost).unwrap().cost <= state.cost);
                let mut s = &state;
                while s.id != 0 {
                    println!(
                        "#{}{}.{}.{}.{}.{}{}#",
                        s.state[0],
                        s.state[1],
                        s.state[2],
                        s.state[3],
                        s.state[4],
                        s.state[5],
                        s.state[6]
                    );
                    println!(
                        "###{}#{}#{}#{}###",
                        s.rooms[0][0], s.rooms[1][0], s.rooms[2][0], s.rooms[3][0]
                    );
                    println!(
                        "  #{}#{}#{}#{}#",
                        s.rooms[0][1], s.rooms[1][1], s.rooms[2][1], s.rooms[3][1]
                    );
                    println!("  ######### {}", s.cost);
                    s = expanded.iter().find(|p| p.id == s.pre).unwrap();
                }
                return state.cost;
            }
            if point < state.heuristics() {
                point = state.heuristics();
                println!(
                    "{:>6}/{:>6}, {:?} {:?}; {:>8}",
                    state.cost,
                    point,
                    state.state.iter().collect::<String>(),
                    state
                        .rooms
                        .iter()
                        .map(|r| r.iter().collect::<String>())
                        .collect::<Vec<_>>(),
                    expanded.len(),
                );
            }
            let nn = updated.len();
            updated.retain(|s| s.id != state.id);
            debug_assert_eq!(nn, updated.len() + 1);
            for mut news in state.neighbor_states() {
                // println!("-- {:?} {:?}", news.state, news.rooms);
                if let Some(found) = expanded.iter_mut().find(|e| **e == news) {
                    if news.cost < found.cost {
                        if let Some(found2) = updated.iter_mut().find(|e| **e == news) {
                            debug_assert_eq!(found2.cost, found.cost);
                            found2.cost = news.cost;
                            found2.pre = news.pre;
                            found.cost = news.cost;
                            found.pre = news.pre;
                            continue;
                        }
                        news.id = found.id;
                        found.cost = news.cost;
                        found.pre = news.pre;
                        // debug_assert!(updated.iter().all(|s| *s != news));
                        updated.push(news);
                    }
                } else {
                    news.id = id_counter;
                    id_counter += 1;
                    debug_assert!(expanded.iter().all(|s| *s != news));
                    expanded.push(news.clone());
                    debug_assert!(updated.iter().all(|s| *s != news));
                    updated.push(news);
                }
            }
            // if 120 < id_counter {
            // panic!();
            // }
        }
        0
    }
    fn part2(&mut self) -> Self::Output2 {
        let goal: P1 = P1 {
            id: 0,
            cost: 0,
            state: ['.', '.', '.', '.', '.', '.', '.'],
            rooms: [
                vec!['A', 'A', 'A', 'A'],
                vec!['B', 'B', 'B', 'B'],
                vec!['C', 'C', 'C', 'C'],
                vec!['D', 'D', 'D', 'D'],
            ],
            pre: 0,
        };
        let init = P1 {
            id: 0,
            cost: 0,
            state: goal.state,
            rooms: [
                vec![self.line[0], 'D', 'D', self.line[4]],
                vec![self.line[1], 'C', 'B', self.line[5]],
                vec![self.line[2], 'B', 'A', self.line[6]],
                vec![self.line[3], 'A', 'C', self.line[7]],
            ],
            pre: 0,
        };
        let mut point: isize = init.heuristics();
        let mut expanded: Vec<P1> = vec![init];
        let mut updated: Vec<P1> = expanded.clone();
        let mut id_counter = 0;
        while let Some(rstate) = updated.iter().min_by_key(|s| s.cost) {
            let state = rstate.clone();
            if state == goal {
                // debug_assert!(updated.iter().min_by_key(|s| s.cost).unwrap().cost <= state.cost);
                let mut s = &state;
                while s.id != 0 {
                    println!(
                        "#{}{}.{}.{}.{}.{}{}#",
                        s.state[0],
                        s.state[1],
                        s.state[2],
                        s.state[3],
                        s.state[4],
                        s.state[5],
                        s.state[6]
                    );
                    println!(
                        "###{}#{}#{}#{}###",
                        s.rooms[0][0], s.rooms[1][0], s.rooms[2][0], s.rooms[3][0]
                    );
                    println!(
                        "  #{}#{}#{}#{}#",
                        s.rooms[0][1], s.rooms[1][1], s.rooms[2][1], s.rooms[3][1]
                    );
                    println!(
                        "  #{}#{}#{}#{}#",
                        s.rooms[0][2], s.rooms[1][2], s.rooms[2][2], s.rooms[3][2]
                    );
                    println!(
                        "  #{}#{}#{}#{}#",
                        s.rooms[0][3], s.rooms[1][3], s.rooms[2][3], s.rooms[3][3]
                    );
                    println!("  ######### {}", s.cost);
                    s = expanded.iter().find(|p| p.id == s.pre).unwrap();
                }
                return state.cost;
            }
            if point < state.heuristics() {
                point = state.heuristics();
                println!(
                    "{:>6}({:>6}), {:?} {:?}, {:>8}",
                    state.cost,
                    point,
                    state.state.iter().collect::<String>(),
                    state
                        .rooms
                        .iter()
                        .map(|r| r.iter().collect::<String>())
                        .collect::<Vec<_>>(),
                    expanded.len(),
                );
            }
            let nn = updated.len();
            updated.retain(|s| s.id != state.id);
            debug_assert_eq!(nn, updated.len() + 1);

            for mut news in state.neighbor_states() {
                if let Some(found) = expanded.iter_mut().find(|e| **e == news) {
                    if news.cost < found.cost {
                        if let Some(found2) = updated.iter_mut().find(|e| **e == news) {
                            debug_assert_eq!(found2.cost, found.cost);
                            found2.cost = news.cost;
                            found2.pre = news.pre;
                            found.cost = news.cost;
                            found.pre = news.pre;
                            continue;
                        }
                        news.id = found.id;
                        found.cost = news.cost;
                        found.pre = news.pre;
                        // debug_assert!(updated.iter().all(|s| *s != news));
                        updated.push(news);
                    }
                } else {
                    news.id = id_counter;
                    id_counter += 1;
                    // debug_assert!(expanded.iter().all(|s| *s != news));
                    expanded.push(news.clone());
                    // debug_assert!(updated.iter().all(|s| *s != news));
                    updated.push(news);
                }
            }
            /*
                        for mut news in state.neighbor_states() {
                            if let Some(found) = updated.iter_mut().find(|e| **e == news) {
                                if news.cost < found.cost {
                                    found.cost = news.cost;
                                    found.pre = news.pre;
                                    // expanded.push(news.clone());
                                    // updated.push(news);
                                }
                            } else {
                                news.id = id_counter;
                                id_counter += 1;
                                expanded.push(news.clone());
                                updated.push(news);
                            }
                        }
            */
        }
        0
    }
}
