//! <https://adventofcode.com/2018/day/23>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]

use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::neighbors,
        line_parser, regex,
    },
    std::{
        cmp::Reverse,
        collections::{BinaryHeap, HashMap, HashSet},
    },
};

type Dim3 = (isize, isize, isize);

const NUM_ROBOTS: usize = 1000;
const DIRS: [Dim3; 6] = [
    (-1, 0, 0),
    (1, 0, 0),
    (0, -1, 0),
    (0, 1, 0),
    (0, 0, -1),
    (0, 0, 1),
];

trait Geometry {
    fn x(&self) -> isize;
    fn y(&self) -> isize;
    fn z(&self) -> isize;
    fn abs_dist(&self) -> usize;
    fn dist(&self, other: &Self) -> usize;
}

impl Geometry for Dim3 {
    fn x(&self) -> isize {
        self.0
    }
    fn y(&self) -> isize {
        self.1
    }
    fn z(&self) -> isize {
        self.2
    }
    fn abs_dist(&self) -> usize {
        self.0.unsigned_abs() + self.1.unsigned_abs() + self.2.unsigned_abs()
    }
    fn dist(&self, other: &Dim3) -> usize {
        (self.0 - other.0).unsigned_abs()
            + (self.1 - other.1).unsigned_abs()
            + (self.2 - other.2).unsigned_abs()
    }
}

type Nanobot = ((isize, isize, isize), usize);

trait InArea {
    fn within_range(&self, target: &Dim3) -> bool;
    fn abs_dist(&self) -> usize;
    fn dist(&self, pos: &Dim3) -> usize;
    fn within_envelop_area(&self, cubic: &Cubic) -> bool;
}

impl InArea for Nanobot {
    fn within_range(&self, target: &Dim3) -> bool {
        self.dist(target) <= self.1
    }
    fn abs_dist(&self) -> usize {
        self.0.abs_dist()
    }
    fn dist(&self, pos: &Dim3) -> usize {
        self.0.dist(pos)
    }
    fn within_envelop_area(&self, cubic: &Cubic) -> bool {
        (((self.0 .1 - cubic.center.0) as f64).powf(2.0)
            + ((self.0 .1 - cubic.center.1) as f64).powf(2.0)
            + ((self.0 .2 - cubic.center.2) as f64).powf(2.0))
        .sqrt()
            < (self.1 + cubic.radius) as f64
    }
}

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Nanobot>,
}

#[aoc(2018, 23)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        let parser = regex!(r"^pos=<(-?\d+),(-?\d+),(-?\d+)>, r=(-?\d+)$");
        let segment = parser.captures(block).ok_or(ParseError)?;
        self.line.push((
            (
                segment[1].parse::<isize>()?,
                segment[2].parse::<isize>()?,
                segment[3].parse::<isize>()?,
            ),
            segment[4].parse::<usize>()?,
        ));
        Ok(())
    }
    fn after_insert(&mut self) {
        dbg!(self.line.len());
    }
    fn part1(&mut self) -> Self::Output1 {
        let strongest: (&usize, &Dim3) = self.line.iter().map(|(p, r)| (r, p)).max().unwrap();
        self.line
            .iter()
            .filter(|(p, r)| strongest.1.dist(p) <= *strongest.0)
            .count()
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut best = Cubic {
            center: (12, 12, 12),
            radius: 2,
            affecting: 0,
        };
        best.setup_membership(self);
        dbg!(best.affecting);
        dbg!(best.is_coherent(self));
        let mut start = Cubic {
            center: (0, 0, 0),
            radius: 32,
            affecting: 0,
        };
        start.radius = self
            .line
            .iter()
            .map(|r| r.abs_dist())
            .max()
            .unwrap()
            .next_power_of_two();
        start.setup_membership(self);
        dbg!(start.radius, start.affecting);
        let mut to_visit: BinaryHeap<Reverse<Cubic>> = BinaryHeap::new();
        let mut max_value = 1;
        let mut max_position = (0, 0, 0);
        let mut best_distance = 0;
        to_visit.push(Reverse(start));
        let mut out = 0;
        let mut rin = 1;
        while let Some(Reverse(mut p)) = to_visit.pop() {
            out += 1;
            // if 2 <= p.radius
            //     && 0 < p.center.0
            //     && 0 < p.center.1
            //     && 0 < p.center.2
            //     && 3 <= p.max_bound()
            // {
            //     println!("---{:?}({}) {}", p.center, p.radius, p.max_bound());
            // }
            // if 1 < p.affecting {
            //     dbg!(p.affecting);
            // }
            // println!(
            //     "c:{:?}, r:{}, max: {}, inc: {}",
            //     p.center,
            //     p.radius,
            //     p.max_bound(),
            //     p.affecting
            // );
            if p.affecting < max_value
                || (p.affecting == max_value && best_distance < p.closest().abs_dist())
            {
                continue;
            }
            if 8192 * 8192 < p.radius && max_value <= p.affecting {
                println!(
                    ":::{:?}(d={}, r={}) {}",
                    p.center,
                    p.closest().abs_dist(),
                    p.radius,
                    p.affecting
                );
            }
            // if to_visit.len() % 1000 == 0 {
            //     dbg!(to_visit.len());
            // }
            if let Some(n) = p.is_coherent(self) {
                if 0 < p.radius {
                    dbg!(n, p.center);
                }
                match max_value.cmp(&n) {
                    std::cmp::Ordering::Less => {
                        max_value = n;
                        max_position = p.closest();
                        best_distance = max_position.abs_dist();
                        dbg!(max_value, best_distance);
                    }
                    std::cmp::Ordering::Equal => {
                        let d = p.closest();
                        if d.abs_dist() < max_position.abs_dist() {
                            max_position = d;
                            best_distance = max_position.abs_dist();
                            dbg!(best_distance);
                        }
                    }
                    _ => (),
                }
                continue;
            } else {
                let c = self.count(&p.center);
                match max_value.cmp(&c) {
                    std::cmp::Ordering::Less => {
                        max_value = c;
                        max_position = p.center;
                        best_distance = p.center.abs_dist();
                        dbg!(max_value, best_distance);
                    }
                    std::cmp::Ordering::Equal => {
                        if p.center.abs_dist() < max_position.abs_dist() {
                            max_position = p.center;
                            best_distance = p.center.abs_dist();
                            dbg!(best_distance);
                        }
                    }
                    _ => (),
                }
            }
            if p.radius == 0 {
                continue;
            }
            for sub in p.divide().iter() {
                let mut q = sub.clone();
                q.affecting = 1;
                q.setup_membership(self);
                // if 2 < q.affecting {
                //     println!("{:?}, {}", q.center, q.max_bound());
                // }
                // record_list.push(q.center);
                to_visit.push(Reverse(q));
                rin += 1;
            }
        }
        dbg!(&max_position);
        // let mut r = record.iter().collect::<Vec<_>>();
        // r.sort();
        // println!("{:?}", r);
        // println!("{:?}", record_list);
        dbg!(rin, out);
        max_position.dist(&(0, 0, 0))
    }
}
impl Puzzle {
    fn count(&self, pos: &Dim3) -> usize {
        self.line.iter().filter(|r| r.within_range(pos)).count()
    }
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct Cubic {
    center: Dim3,
    radius: usize,
    affecting: usize,
}

impl Cubic {
    fn setup_membership(&mut self, world: &Puzzle) {
        self.affecting = world
            .line
            .iter()
            .filter(|r| r.within_envelop_area(self))
            .count();
    }
    fn is_coherent(&mut self, world: &Puzzle) -> Option<usize> {
        if self.radius == 0 {
            return Some(world.count(&self.center));
        }
        let overestimate = world
            .line
            .iter()
            .map(|r| r.within_envelop_area(self))
            .collect::<Vec<_>>();
        for (i, robot) in world.line.iter().enumerate() {
            for dir in DIRS.iter() {
                let pos = (
                    self.center.0 + dir.0 * self.radius as isize,
                    self.center.1 + dir.1 * self.radius as isize,
                    self.center.2 + dir.2 * self.radius as isize,
                );
                if overestimate[i] != robot.within_range(&pos) {
                    return None;
                }
            }
        }
        Some(overestimate.iter().filter(|b| **b).count())
    }
    fn divide(&self) -> Vec<Cubic> {
        let c = self.center;
        if self.radius == 1 {
            return vec![
                Cubic {
                    center: (c.0 - 1, c.1 - 1, c.2 - 1),
                    ..Cubic::default()
                },
                Cubic {
                    center: (c.0 - 1, c.1 + 1, c.2 - 1),
                    ..Cubic::default()
                },
                Cubic {
                    center: (c.0 + 1, c.1 - 1, c.2 - 1),
                    ..Cubic::default()
                },
                Cubic {
                    center: (c.0 + 1, c.1 + 1, c.2 - 1),
                    ..Cubic::default()
                },
                Cubic {
                    center: (c.0 - 1, c.1 - 1, c.2 + 1),
                    ..Cubic::default()
                },
                Cubic {
                    center: (c.0 - 1, c.1 + 1, c.2 + 1),
                    ..Cubic::default()
                },
                Cubic {
                    center: (c.0 + 1, c.1 - 1, c.2 + 1),
                    ..Cubic::default()
                },
                Cubic {
                    center: (c.0 + 1, c.1 + 1, c.2 + 1),
                    ..Cubic::default()
                },
            ];
        }
        let r = (self.radius / 2) as isize;
        let radius = self.radius / 2;
        assert!(0 < radius);
        vec![
            Cubic {
                center: (c.0 - r, c.1 - r, c.2 - r),
                radius,
                ..Cubic::default()
            },
            Cubic {
                center: (c.0 - r, c.1 + r, c.2 - r),
                radius,
                ..Cubic::default()
            },
            Cubic {
                center: (c.0 + r, c.1 - r, c.2 - r),
                radius,
                ..Cubic::default()
            },
            Cubic {
                center: (c.0 + r, c.1 + r, c.2 - r),
                radius,
                ..Cubic::default()
            },
            Cubic {
                center: (c.0 - r, c.1 - r, c.2 + r),
                radius,
                ..Cubic::default()
            },
            Cubic {
                center: (c.0 - r, c.1 + r, c.2 + r),
                radius,
                ..Cubic::default()
            },
            Cubic {
                center: (c.0 + r, c.1 - r, c.2 + r),
                radius,
                ..Cubic::default()
            },
            Cubic {
                center: (c.0 + r, c.1 + r, c.2 + r),
                radius,
                ..Cubic::default()
            },
        ]
    }
    fn closest(&self) -> Dim3 {
        if self.radius == 0 {
            self.center
        } else {
            let mut d = usize::MAX;
            let mut p = (0, 0, 0);
            for dir in DIRS.iter() {
                let pos = (
                    self.center.0 + dir.0,
                    self.center.1 + dir.1,
                    self.center.2 + dir.2,
                );
                let dist = pos.dist(&(0, 0, 0));
                if dist < d {
                    d = dist;
                    p = pos;
                }
            }
            p
        }
    }
}

impl Geometry for Cubic {
    fn x(&self) -> isize {
        self.center.0
    }
    fn y(&self) -> isize {
        self.center.1
    }
    fn z(&self) -> isize {
        self.center.2
    }
    fn abs_dist(&self) -> usize {
        self.center.0.unsigned_abs() + self.center.1.unsigned_abs() + self.center.2.unsigned_abs()
    }
    fn dist(&self, other: &Cubic) -> usize {
        unimplemented!()
    }
}

impl PartialOrd for Cubic {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.affecting.partial_cmp(&other.affecting)
        // self.abs_dist().partial_cmp(&other.abs_dist())
    }
}

impl Ord for Cubic {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.affecting.cmp(&other.affecting)
        // self.abs_dist().cmp(&other.abs_dist())
    }
}
