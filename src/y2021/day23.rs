//! <https://adventofcode.com/2021/day/23>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]

use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::neighbors,
        line_parser,
    },
    lazy_static::lazy_static,
    regex::Regex,
    std::cmp::{Ord, Ordering, PartialOrd},
    std::collections::HashMap,
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
    rooms: [[char; 2]; 4],
    pre: usize,
}

impl PartialOrd for P1 {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.cost.partial_cmp(&other.cost)
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

const GOAL: P1 = P1 {
    id: 0,
    cost: 0,
    state: ['.', '.', '.', '.', '.', '.', '.'],
    rooms: [['A', 'A'], ['B', 'B'], ['C', 'C'], ['D', 'D']],
    pre: 0,
};

trait Game {
    fn check_them(&self, msg: &str);
    fn reach_goal(&self) -> Option<usize>;
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
                    (c, r1) if r1 == target => 9 * point,
                    ('.', '.') => 0,
                    ('.', r1) => -10 * point,
                    (r0, r1) => -11 * point,
                }
            })
            .sum()
    }
    fn check_them(&self, msg: &str) {
        assert!(
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
    }
    fn reach_goal(&self) -> Option<usize> {
        (*self == GOAL).then(|| self.cost)
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
        let mut result: Vec<Self> = Vec::new();
        // move out from a room
        for (i, r) in self.rooms.iter().enumerate() {
            let satisfied = (b'A' + i as u8) as char;
            if r[0] == '.' {
                continue;
            }
            if r[0] == satisfied && r[1] == satisfied {
                continue;
            }
            for (j, v) in self.state.iter().enumerate() {
                if !self.walkable_between(j, i, None) {
                    continue;
                }
                let mut news = (*self).clone();
                assert!(news.state[j] == '.', "i {}, j {} {:?}", i, j, news);
                news.state[j] = r[0];
                news.rooms[i][0] = '.';
                news.cost += 10usize.pow((r[0] as u8 - b'A') as u32) * DIST_FROM_ROOM[i][j];
                news.check_them("1");
                news.pre = self.id;
                result.push(news);
            }
        }
        // move out from a room bottom
        for (i, r) in self.rooms.iter().enumerate() {
            let satisfied = (b'A' + i as u8) as char;
            if r[0] != '.' {
                continue;
            }
            if r[1] == '.' || r[1] == satisfied {
                continue;
            }
            for (j, v) in self.state.iter().enumerate() {
                if !self.walkable_between(j, i, None) {
                    continue;
                }
                let mut news = (*self).clone();
                news.state[j] = r[1];
                news.rooms[i][1] = '.';
                news.cost += 10usize.pow((r[1] as u8 - b'A') as u32) * (DIST_FROM_ROOM[i][j] + 1);
                news.check_them("2");
                news.pre = self.id;
                result.push(news);
            }
        }
        // move in to a room
        for (i, amph) in self.state.iter().enumerate() {
            if *amph == '.' {
                continue;
            }
            for (j, r) in self.rooms.iter().enumerate() {
                if j != (*amph as u8 - b'A') as usize {
                    continue;
                }
                if r[0] != '.' {
                    continue;
                }
                if !self.walkable_between(i, j, Some(*amph)) {
                    continue;
                }
                if r[1] == '.' {
                    let mut news = (*self).clone();
                    news.state[i] = '.';
                    news.rooms[j][1] = *amph;
                    news.cost +=
                        10usize.pow((*amph as u8 - b'A') as u32) * (DIST_FROM_ROOM[j][i] + 1);
                    news.pre = self.id;
                    result.push(news);
                } else {
                    let mut news = (*self).clone();
                    news.state[i] = '.';
                    news.rooms[j][0] = *amph;
                    news.cost += 10usize.pow((*amph as u8 - b'A') as u32) * DIST_FROM_ROOM[j][i];
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
    fn after_insert(&mut self) {
        self.line.retain(|c| *c != '#' && *c != '.');
        dbg!(&self.line.len());
    }
    fn part1(&mut self) -> Self::Output1 {
        let init = P1 {
            id: 0,
            cost: 0,
            state: GOAL.state,
            rooms: [
                [self.line[0], self.line[4]],
                [self.line[1], self.line[5]],
                [self.line[2], self.line[6]],
                [self.line[3], self.line[7]],
            ],
            pre: 0,
        };
        let mut point: isize = init.heuristics();
        let mut expanded: Vec<P1> = vec![init];
        let mut updated: Vec<P1> = expanded.clone();
        let mut id_counter = 0;
        while let Some(rstate) = updated.iter().min_by_key(|s| s.cost) {
            let state = rstate.clone();
            if state == GOAL {
                assert!(updated.iter().min_by_key(|s| s.cost).unwrap().cost <= state.cost);
                let mut s = &state;
                while s.id != 0 {
                    println!("#{}{}.{}.{}.{}.{}{}#", s.state[0], s.state[1], s.state[2], s.state[3], s.state[4], s.state[5], s.state[6]);
                    println!("###{}#{}#{}#{}###", s.rooms[0][0], s.rooms[1][0], s.rooms[2][0], s.rooms[3][0]);
                    println!("  #{}#{}#{}#{}#", s.rooms[0][1], s.rooms[1][1], s.rooms[2][1], s.rooms[3][1]);
                    println!("  ######### {}", s.cost);
                    s = expanded.iter().find(|p| p.id == s.pre).unwrap();
                }
                return state.cost;
            }
            if point < state.heuristics() {
                point = state.heuristics();
                println!("{:>6}({:>6}), {:?} {:?}", state.cost, point, state.state, state.rooms);
            }
            let nn = updated.len();
            updated.retain(|s| s.id != state.id);
            assert_eq!(nn, updated.len() + 1);
            for mut news in state.neighbor_states() {
                if let Some(found) = expanded.iter_mut().find(|e| **e == news) {
                    if news.cost < found.cost {
                        if let Some(found2) = updated.iter_mut().find(|e| **e == news) {
                            assert_eq!(found2.cost, found.cost);
                            found2.cost = news.cost;
                            found2.pre = news.pre;
                            found.cost = news.cost;
                            found.pre = news.pre;
                            continue;
                        }
                        news.id = found.id;
                        found.cost = news.cost;
                        found.pre = news.pre;
                        // assert!(updated.iter().all(|s| *s != news));
                        updated.push(news);
                    }
                } else {
                    news.id = id_counter;
                    id_counter += 1;
                    assert!(expanded.iter().all(|s| *s != news));
                    expanded.push(news.clone());
                    assert!(updated.iter().all(|s| *s != news));
                    updated.push(news);
                }
            }
        }
        0
    }
    fn part2(&mut self) -> Self::Output2 {
        0
    }
}
