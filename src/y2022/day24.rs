//! <https://adventofcode.com/2022/day/24>
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::{Dim2, GeometricMath},
    },
    std::{
        cmp::Reverse,
        collections::{BinaryHeap, HashMap, HashSet},
    },
};

type Dim = Dim2<usize>;

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Puzzle {
    line: Vec<Vec<char>>,
    map: HashMap<Dim, char>,
    width: usize,
    height: usize,
    start: Dim,
    goal: Dim,
    blizzard_r: Vec<Dim>,
    blizzard_d: Vec<Dim>,
    blizzard_l: Vec<Dim>,
    blizzard_u: Vec<Dim>,
}

impl Puzzle {
    fn is_open(&self, time: usize, position: &Dim) -> bool {
        self.blizzard_r
            .iter()
            .filter(|(y, _)| *y == position.0)
            .all(|(_, init_x)| (init_x - 1 + time) % self.width + 1 != position.1)
            && self
                .blizzard_d
                .iter()
                .filter(|(_, x)| *x == position.1)
                .all(|(init_y, _)| (init_y - 1 + time) % self.height + 1 != position.0)
            && self
                .blizzard_l
                .iter()
                .filter(|(y, _)| *y == position.0)
                .all(|(_, init_x)| {
                    (init_x - 1 + self.width * time - time) % self.width + 1 != position.1
                })
            && self
                .blizzard_u
                .iter()
                .filter(|(_, x)| *x == position.1)
                .all(|(init_y, _)| {
                    (init_y - 1 + self.height * time - time) % self.height + 1 != position.0
                })
    }
}

#[aoc(2022, 24)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.line.push(block.chars().collect::<Vec<char>>());
        Ok(())
    }
    fn end_of_data(&mut self) {
        self.height = self.line.len() - 2;
        self.width = self.line[0].len() - 2;
        self.start.1 = self.line[0]
            .iter()
            .enumerate()
            .find(|(_, c)| **c == '.')
            .unwrap()
            .0;
        self.goal.0 = self.line.len() - 1;
        self.goal.1 = self
            .line
            .last()
            .unwrap()
            .iter()
            .enumerate()
            .find(|(_, c)| **c == '.')
            .unwrap()
            .0;
        for (j, l) in self.line.iter().enumerate() {
            for (i, c) in l.iter().enumerate() {
                match c {
                    '>' => self.blizzard_r.push((j, i)),
                    'v' => self.blizzard_d.push((j, i)),
                    '<' => self.blizzard_l.push((j, i)),
                    '^' => self.blizzard_u.push((j, i)),
                    _ => (),
                }
                self.map.insert((j, i), *c);
            }
        }
    }
    fn serialize(&self) -> Option<String> {
        // let time = 13;
        // dbg!(time);
        // for (j, l) in self.line.iter().enumerate() {
        //     for (i, c) in l.iter().enumerate() {
        //         if *c == '#' {
        //             print!("#");
        //         } else if self.is_open(time, &(j, i)) {
        //             print!(".");
        //         } else {
        //             print!("*");
        //         }
        //     }
        //     println!();
        // }
        serde_json::to_string(&self.line).ok()
    }
    fn part1(&mut self) -> Self::Output1 {
        self.search(0, &self.start, &self.goal)
    }
    fn part2(&mut self) -> Self::Output2 {
        let part1 = self.search(0, &self.start, &self.goal);
        let part2 = self.search(part1, &self.goal, &self.start);
        self.search(part2, &self.start, &self.goal)
    }
}
impl Puzzle {
    fn search(&self, start_time: usize, start: &Dim, goal: &Dim) -> usize {
        let boundary = Some((self.height + 2, self.width + 2));
        #[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub struct State {
            expected: usize,
            time: usize,
            position: Dim,
        }
        let mut to_visit: BinaryHeap<Reverse<State>> = BinaryHeap::new();
        let init = State {
            expected: goal.0.abs_diff(start.0) + goal.1.abs_diff(start.1),
            time: start_time,
            position: *start,
        };
        let mut visited: HashSet<State> = HashSet::new();
        to_visit.push(Reverse(init.clone()));
        visited.insert(init);
        while let Some(Reverse(state)) = to_visit.pop() {
            if state.position == *goal {
                return state.time;
            }
            let time = state.time + 1;
            for next_position in state.position.neighbors(boundary).iter() {
                if self.map.get(next_position) == Some(&'#') {
                    continue;
                }
                if self.is_open(time, next_position) {
                    let next = State {
                        expected: time
                            + goal.0.abs_diff(next_position.0)
                            + goal.1.abs_diff(next_position.1),
                        time,
                        position: *next_position,
                    };
                    if !visited.contains(&next) {
                        to_visit.push(Reverse(next.clone()));
                        visited.insert(next);
                    }
                }
            }
            if self.is_open(time, &state.position) {
                let next = State {
                    expected: state.expected + 1,
                    time,
                    position: state.position,
                };
                if !visited.contains(&next) {
                    to_visit.push(Reverse(next.clone()));
                    visited.insert(next);
                }
            }
        }
        1
    }
}
