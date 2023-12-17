//! <https://adventofcode.com/2023/day/17>
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::{Dim2, Direction, GeometricAddition, GeometricRotation},
    },
    std::{
        cmp::Reverse,
        collections::{BinaryHeap, HashMap},
    },
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
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
    domain: Dim2<usize>,
}

impl Crucible {
    fn possible_dirs(&self) -> Vec<Crucible> {
        let mut res: Vec<Crucible> = Vec::new();
        // go straight
        if self.dist < 2 {
            if let Some(p) = <Dim2<usize> as GeometricAddition<usize>>::move_to(
                self.pos,
                self.dir.as_vec2(),
                self.domain.0,
                self.domain.1,
            ) {
                let mut c = self.clone();
                c.pos = p;
                c.dist += 1;
                res.push(c);
            }
        }
        // turn right
        let dir = GeometricRotation::turn_right(&self.dir);
        if let Some(p) = <Dim2<usize> as GeometricAddition<usize>>::move_to(
            self.pos,
            dir.as_vec2(),
            self.domain.0,
            self.domain.1,
        ) {
            let mut c = self.clone();
            c.pos = p;
            c.dir = dir;
            c.dist = 0;
            res.push(c);
        }
        // turn left
        let dir = GeometricRotation::turn_left(&self.dir);
        if let Some(p) = <Dim2<usize> as GeometricAddition<usize>>::move_to(
            self.pos,
            dir.as_vec2(),
            self.domain.0,
            self.domain.1,
        ) {
            let mut c = self.clone();
            c.pos = p;
            c.dir = dir;
            c.dist = 0;
            res.push(c);
        }
        res
    }
    fn possible_dirs_for_ultra_cruucible(&self) -> Vec<Crucible> {
        let mut res: Vec<Crucible> = Vec::new();
        // go straight
        if self.dist < 10 {
            if let Some(p) = <Dim2<usize> as GeometricAddition<usize>>::move_to(
                self.pos,
                self.dir.as_vec2(),
                self.domain.0,
                self.domain.1,
            ) {
                let mut c = self.clone();
                c.pos = p;
                c.dist += 1;
                res.push(c);
            }
            if self.dist < 4 {
                return res;
            }
        }
        // turn right
        let dir = GeometricRotation::turn_right(&self.dir);
        let q = dir.as_vec2();
        if let Some(p) = <Dim2<usize> as GeometricAddition<usize>>::move_to(
            self.pos,
            q,
            self.domain.0,
            self.domain.1,
        ) {
            let mut c = self.clone();
            c.pos = p;
            c.dir = dir;
            c.dist = 1;
            res.push(c);
        }
        // turn left
        let dir = GeometricRotation::turn_left(&self.dir);
        let q = dir.as_vec2();
        if let Some(p) = <Dim2<usize> as GeometricAddition<usize>>::move_to(
            self.pos,
            q,
            self.domain.0,
            self.domain.1,
        ) {
            let mut c = self.clone();
            c.pos = p;
            c.dir = dir;
            c.dist = 1;
            res.push(c);
        }
        res
    }
}
#[aoc(2023, 17)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.line.push(
            block
                .trim()
                .bytes()
                .map(|c| (c as u8 - b'0') as usize)
                .collect::<Vec<_>>(),
        );
        Ok(())
    }
    // fn end_of_data(&mut self) { dbg!(&self.line); }
    fn part1(&mut self) -> Self::Output1 {
        let height = self.line.len();
        let width = self.line[0].len();
        let goal = (height - 1, width - 1);
        let mut to_visit: BinaryHeap<Reverse<Crucible>> = BinaryHeap::new();
        // mapping (pos, from) => (cost, range, route)
        let mut visited: HashMap<(Dim2<usize>, Direction), (usize, usize)> = HashMap::new();
        let mut cost = self
            .line
            .iter()
            .map(|v| v.iter().sum::<usize>())
            .sum::<usize>();
        let start = Crucible {
            estimate: 9 * height + width,
            cost: 0,
            pos: (0, 0),
            dir: Direction::EAST,
            dist: 0,
            domain: (height, width),
        };
        to_visit.push(Reverse(start));
        while let Some(Reverse(c)) = to_visit.pop() {
            if c.dist == 0 {
                if let Some(d) = visited.get(&(c.pos, c.dir)) {
                    if d.0 <= c.cost && d.1 <= c.dist {
                        continue;
                    }
                }
            }
            if c.pos == goal || cost < c.cost {
                if c.cost < cost {
                    cost = c.cost;
                }
                continue;
            }
            if c.dist == 0 {
                visited.insert((c.pos, c.dir), (c.cost, c.dist));
            }
            let mut cands = c.possible_dirs();
            while let Some(mut cand) = cands.pop() {
                cand.cost += self.line[cand.pos.0][cand.pos.1];
                cand.estimate = cand.cost + 9 * (goal.0 - cand.pos.0 + goal.1 - cand.pos.1);
                to_visit.push(Reverse(cand));
            }
        }
        cost
    }
    fn part2(&mut self) -> Self::Output2 {
        let height = self.line.len();
        let width = self.line[0].len();
        let goal = (height - 1, width - 1);
        let mut to_visit: BinaryHeap<Reverse<Crucible>> = BinaryHeap::new();
        // mapping (pos, from) => (cost, range, route)
        let mut visited: HashMap<(Dim2<usize>, Direction), (usize, usize)> = HashMap::new();
        let mut cost = 1359;
        let start = Crucible {
            estimate: 9 * height + width,
            cost: 0,
            pos: (0, 0),
            dir: Direction::EAST,
            dist: 0,
            domain: (height, width),
        };
        to_visit.push(Reverse(start));
        while let Some(Reverse(c)) = to_visit.pop() {
            if 4 <= c.dist {
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
                if c.cost < cost && 4 <= c.dist {
                    cost = dbg!(c.cost);
                }
                dbg!(to_visit.len());
                continue;
            }
            if 4 <= c.dist {
                visited.insert((c.pos, c.dir), (c.cost, c.dist));
            }
            let mut cands = c.possible_dirs_for_ultra_cruucible();
            while let Some(mut cand) = cands.pop() {
                cand.cost += self.line[cand.pos.0][cand.pos.1];
                cand.estimate = cand.cost + 9 * (goal.0 - cand.pos.0 + goal.1 - cand.pos.1);
                to_visit.push(Reverse(cand));
            }
        }
        cost
    }
}
