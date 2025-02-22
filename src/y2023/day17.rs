//! <https://adventofcode.com/2023/day/17>
use {
    crate::{
        framework::{AdventOfCode, ParseError, aoc},
        geometric::{Dim2, Direction, GeometricAddition, GeometricRotation},
    },
    std::{
        cmp::Reverse,
        collections::{BinaryHeap, HashMap},
    },
};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Vec<usize>>,
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Crucible {
    estimate: usize,
    cost: usize,
    pos: Dim2<usize>,
    dir: Direction,
    dist: usize,
}

impl Crucible {
    fn possible_dirs(
        &self,
        threshold1: usize,
        threshold2: usize,
        height: usize,
        width: usize,
    ) -> Vec<Crucible> {
        let mut res: Vec<Crucible> = Vec::new();
        // go straight
        if self.dist < threshold1 {
            if let Some(p) = self.pos.move_to(self.dir.as_vec2(), height, width) {
                let mut c = self.clone();
                c.pos = *p;
                c.dist += 1;
                res.push(c);
            }
            if self.dist < threshold2 {
                return res;
            }
        }
        // turn right
        let dir = GeometricRotation::turn_right(&self.dir);
        if let Some(p) = self.pos.move_to(dir.as_vec2(), height, width) {
            let mut c = self.clone();
            c.pos = *p;
            c.dir = dir;
            c.dist = 1;
            res.push(c);
        }
        // turn left
        let dir = GeometricRotation::turn_left(&self.dir);
        if let Some(p) = self.pos.move_to(dir.as_vec2(), height, width) {
            let mut c = self.clone();
            c.pos = *p;
            c.dir = dir;
            c.dist = 1;
            res.push(c);
        }
        res
    }
}

#[aoc(2023, 17)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, input: &str) -> Result<(), ParseError> {
        self.line = input
            .lines()
            .map(|l| l.bytes().map(|c| (c - b'0') as usize).collect())
            .collect();
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        self.search(false)
    }
    fn part2(&mut self) -> Self::Output2 {
        self.search(true)
    }
}

impl Puzzle {
    fn search(&mut self, setting2: bool) -> usize {
        let threshold = if setting2 { 4 } else { 0 };
        let threshold2 = if setting2 { 10 } else { 3 };
        let height = self.line.len();
        let width = self.line[0].len();
        let goal = (height - 1, width - 1);
        let mut to_visit: BinaryHeap<Reverse<Crucible>> = BinaryHeap::new();
        // mapping (pos, from) => (cost, range)
        let mut visited: HashMap<(Dim2<usize>, Direction), (usize, usize)> = HashMap::new();
        let mut cost = 1359;
        let start = Crucible {
            estimate: height + width,
            cost: 0,
            pos: (0, 0),
            dir: Direction::EAST,
            dist: 0,
        };
        to_visit.push(Reverse(start));
        while let Some(Reverse(c)) = to_visit.pop() {
            if threshold <= c.dist {
                if let Some(d) = visited.get(&(c.pos, c.dir)) {
                    if d.0 <= c.cost && d.1 <= c.dist {
                        continue;
                    }
                }
            }
            if cost <= c.cost {
                continue;
            }
            if c.pos == goal {
                if c.cost < cost && threshold <= c.dist {
                    cost = c.cost;
                }
                continue;
            }
            if threshold <= c.dist {
                visited.insert((c.pos, c.dir), (c.cost, c.dist));
            }
            let mut cands = c.possible_dirs(threshold2, threshold, height, width);
            while let Some(mut cand) = cands.pop() {
                cand.cost += self.line[cand.pos.0][cand.pos.1];
                cand.estimate = cand.cost + (goal.0 - cand.pos.0 + goal.1 - cand.pos.1);
                to_visit.push(Reverse(cand));
            }
        }
        cost
    }
}
