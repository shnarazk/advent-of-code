//! <https://adventofcode.com/2022/day/19>

use {
    crate::{
        framework::{AdventOfCode, ParseError, aoc},
        parser::parse_usize,
        progress,
    },
    std::collections::{BinaryHeap, HashMap},
    winnow::{
        ModalResult, Parser,
        ascii::newline,
        combinator::{separated, seq},
    },
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

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Blueprint {
    id: usize,
    trans: [[usize; 4]; 4],
    limits: [usize; 4],
}

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct State {
    mining_power: usize,
    time: usize,
    resources: [usize; 4],
    robots: [usize; 4],
}
impl State {
    /// returns the goodness (mining ability) and bottomline value
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
            if 0 < state.robots[0] {
                let total = state.resources[0] + (limit - state.time) * state.robots[0];
                if num_geodes < total {
                    num_geodes = total;
                    progress!(num_geodes);
                }
            }
            for (i, requires) in self.trans.iter().enumerate() {
                if self.limits[i] <= state.robots[i] {
                    continue;
                }
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
                to_visit.push(next);
            }
        }
        num_geodes
    }
}

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Blueprint>,
}

#[allow(clippy::type_complexity)]
fn parse_line(s: &mut &str) -> ModalResult<(usize, usize, usize, usize, usize, usize, usize)> {
    seq!(
            _: "Blueprint ", parse_usize,
            _: ": Each ore robot costs ", parse_usize,
            _: " ore. Each clay robot costs ", parse_usize,
            _: " ore. Each obsidian robot costs ", parse_usize,
            _: " ore and ", parse_usize,
            _: " clay. Each geode robot costs ", parse_usize,
            _: " ore and ", parse_usize,
            _: " obsidian."
    )
    .parse_next(s)
}

#[allow(clippy::type_complexity)]
fn parse(s: &mut &str) -> ModalResult<Vec<(usize, usize, usize, usize, usize, usize, usize)>> {
    separated(1.., parse_line, newline).parse_next(s)
}

#[aoc(2022, 19)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, mut input: &str) -> Result<(), ParseError> {
        let line = parse(&mut input)?;
        self.line = line
            .iter()
            .map(|(n0, n1, n2, n3, n4, n5, n6)| Blueprint {
                id: *n0,
                trans: [
                    [0, *n6, 0, *n5],
                    [0, 0, *n4, *n3],
                    [0, 0, 0, *n2],
                    [0, 0, 0, *n1],
                ],
                limits: [usize::MAX, *n6, *n4, *n5.max(n3).max(n2.max(n1))],
            })
            .collect::<_>();

        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        self.line.iter().map(|bp| bp.id * bp.profit(24)).sum()
    }
    fn part2(&mut self) -> Self::Output2 {
        self.line.iter().take(3).map(|bp| bp.profit(32)).product()
    }
}
