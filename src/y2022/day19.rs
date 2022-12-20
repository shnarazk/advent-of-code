//! <https://adventofcode.com/2022/day/19>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::neighbors,
        line_parser, regex,
    },
    std::collections::{BinaryHeap, HashMap},
};

trait Calculation {
    fn add(&self, other: &Self) -> Self;
    fn sub(&self, other: &Self) -> Self;
    fn scale(&self, num: usize) -> Self;
}
impl Calculation for [usize; 4] {
    fn add(&self, other: &Self) -> Self {
        [
            self[0] + other[0],
            self[1] + other[1],
            self[2] + other[2],
            self[3] + other[3],
        ]
    }
    fn sub(&self, other: &Self) -> Self {
        [
            self[0] - other[0],
            self[1] - other[1],
            self[2] - other[2],
            self[3] - other[3],
        ]
    }
    fn scale(&self, num: usize) -> Self {
        [self[0] * num, self[1] * num, self[2] * num, self[3] * num]
    }
}

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Blueprint {
    id: usize,
    trans: [[usize; 4]; 4],
}

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct State {
    mining_power: usize,
    // last_geode_robot_birth: usize,
    time: usize,
    resources: [usize; 4],
    robots: [usize; 4],
}
impl State {
    fn value(&self, bp: &Blueprint) -> (usize, usize) {
        let k3 = bp.trans[3][3];
        let k2 = bp.trans[2][3];
        let k1 = bp.trans[1][3] + bp.trans[1][2] * k2;
        let k0 = bp.trans[0][3] + bp.trans[0][1] * k1;
        let d3 = self.robots[3] * k3;
        let d2 = self.robots[2] * k2;
        let d1 = self.robots[1] * k1;
        let d0 = self.robots[0] * k0;
        (
            d0 + d1 + d2 + d3,
            if self.robots[0] == 0 {
                0
            } else {
                (self.robots[0] - 1) * k0
            },
        )
    }
}
impl Blueprint {
    fn profit(&self, limit: usize) -> usize {
        let mut bottom_line: HashMap<usize, usize> = HashMap::new();
        // let mut geode_robot: HashMap<usize, usize> = HashMap::new();
        let mut num_geodes = 0;
        let mut to_visit: BinaryHeap<State> = BinaryHeap::new();
        let init = State {
            time: 1,
            robots: [0, 0, 0, 1],
            resources: [0, 0, 0, 1],
            ..Default::default()
        };
        to_visit.push(init);
        while let Some(state) = to_visit.pop() {
            if state.value(self).0 < *bottom_line.get(&state.time).unwrap_or(&0) {
                continue;
            }
            // if *geode_robot.get(&state.robots[0]).unwrap_or(&usize::MAX)
            //     < state.last_geode_robot_birth
            // {
            //     continue;
            // }
            if 0 < state.robots[0] {
                let total = state.resources[0] + (limit - state.time) * state.robots[0];
                if num_geodes < total {
                    num_geodes = total;
                    dbg!(num_geodes);
                }
            }
            for (i, requires) in self.trans.iter().enumerate() {
                // check if all the required stuffs can be generated
                if !requires
                    .iter()
                    .zip(state.robots.iter())
                    .all(|(req, bot)| *req == 0 || 0 < *bot)
                {
                    continue;
                }
                // So generate a robot after the required time is elapsed
                let mut next = state.clone();
                let time_to_wait: usize = requires
                    .iter()
                    .zip(state.resources.iter().zip(state.robots.iter()))
                    .filter_map(|(req, (res, bot))| {
                        req.checked_sub(*res).map(|t| {
                            if *bot == 0 {
                                t
                            } else if t % bot == 0 {
                                t / bot
                            } else {
                                t / bot + 1
                            }
                        })
                    })
                    .max()
                    .unwrap_or_default();
                next.time += time_to_wait;
                if limit <= next.time {
                    continue;
                }
                next.resources = state
                    .robots
                    .scale(time_to_wait + 1)
                    .add(&next.resources)
                    .sub(requires);
                next.time += 1;
                let mut produces = [0, 0, 0, 0];
                produces[i] = 1;
                next.robots = produces.add(&state.robots);
                {
                    let (v, mut thr) = next.value(self);
                    next.mining_power = v;
                    let e = bottom_line.entry(next.time).or_insert(0);
                    *e = *e.max(&mut thr);
                }
                // if state.robots[0] < next.robots[0] {
                //     if *geode_robot.get(&next.robots[0]).unwrap_or(&usize::MAX) < next.time {
                //         continue;
                //     } else {
                //         geode_robot.insert(next.robots[0], next.time);
                //         next.last_geode_robot_birth = next.time;
                //     }
                // }
                // println!(
                //     "resource: {:?}, robots: {:?} at time {}",
                //     next.resources, next.robots, next.time
                // );
                to_visit.push(next);
            }
        }
        num_geodes
    }
}

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Blueprint>,
}

#[aoc(2022, 19)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        let parser = regex!(
            r"^Blueprint (\d+): Each ore robot costs (\d+) ore. Each clay robot costs (\d+) ore. Each obsidian robot costs (\d+) ore and (\d+) clay. Each geode robot costs (\d+) ore and (\d+) obsidian."
        );
        if let Some(segment) = parser.captures(block) {
            macro_rules! nth {
                ($n: expr) => {
                    segment[$n].parse::<usize>()?
                };
            }
            self.line.push(Blueprint {
                id: segment[1].parse::<_>()?,
                trans: [
                    [0, nth!(7), 0, nth!(6)],
                    [0, 0, nth!(5), nth!(4)],
                    [0, 0, 0, nth!(3)],
                    [0, 0, 0, nth!(2)],
                ],
            });
        }
        Ok(())
    }
    fn after_insert(&mut self) {
        // dbg!(&self.line);
        dbg!(&self.line.len());
    }
    fn part1(&mut self) -> Self::Output1 {
        self.line.iter().map(|bp| bp.id * bp.profit(24)).sum()
    }
    fn part2(&mut self) -> Self::Output2 {
        self.line.iter().map(|bp| bp.profit(32)).product()
    }
}
