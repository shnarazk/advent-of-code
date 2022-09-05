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
    // fn x(&self) -> isize;
    // fn y(&self) -> isize;
    // fn z(&self) -> isize;
    fn abs_dist(&self) -> usize;
    fn dist(&self, other: &Dim3) -> usize;
}

impl Geometry for Dim3 {
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
    fn within_range(&self, target: &Dim3, offset: isize) -> bool;
}

impl InArea for Nanobot {
    fn within_range(&self, target: &Dim3, offset: isize) -> bool {
        self.0.dist(target) as isize <= self.1 as isize + offset
    }
}

impl Geometry for Nanobot {
    fn abs_dist(&self) -> usize {
        self.0.abs_dist()
    }
    fn dist(&self, pos: &Dim3) -> usize {
        self.0.dist(pos)
    }
}

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Nanobot>,
    num_robots: usize,
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
        self.num_robots = self.line.len();
        dbg!(self.num_robots);
    }
    fn part1(&mut self) -> Self::Output1 {
        let strongest: (&usize, &Dim3) = self.line.iter().map(|(p, r)| (r, p)).max().unwrap();
        self.line
            .iter()
            .filter(|(p, r)| strongest.1.dist(p) <= *strongest.0)
            .count()
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut start = Cubic {
            radius: 32,
            ..Cubic::default()
        };
        start.radius = self
            .line
            .iter()
            .map(|r| r.abs_dist())
            .max()
            .unwrap()
            .next_power_of_two();
        start.setup_membership(self);
        dbg!(start.radius, start.completely_inside);
        let mut to_visit: BinaryHeap<Reverse<Cubic>> = BinaryHeap::new();
        let mut max_value = 1;
        let mut max_position = (0, 0, 0);
        let mut best_distance = 0;
        to_visit.push(Reverse(start));
        let mut out = 0;
        let mut rin = 1;
        while let Some(Reverse(mut p)) = to_visit.pop() {
            out += 1;
            if p.affecting(self) < max_value
            // || (p.affecting(self) == max_value && best_distance < p.closest().abs_dist())
            {
                continue;
            }
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
                q.setup_membership(self);
                // if 2 < q.affecting {
                //     println!("{:?}, {}", q.center, q.max_bound());
                // }
                // record_list.push(q.center);
                to_visit.push(Reverse(q));
                rin += 1;
            }
        }
        dbg!(&max_position, best_distance);
        // let mut r = record.iter().collect::<Vec<_>>();
        // r.sort();
        // println!("{:?}", r);
        // println!("{:?}", record_list);
        dbg!(rin, out);
        best_distance
    }
}
impl Puzzle {
    fn count(&self, pos: &Dim3) -> usize {
        self.line.iter().filter(|r| r.within_range(pos, 0)).count()
    }
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct Cubic {
    center: Dim3,
    radius: usize,
    completely_inside: usize,
    completely_outside: usize,
    not_affect: usize,
}

impl Cubic {
    fn affecting(&self, world: &Puzzle) -> usize {
        world.num_robots - self.completely_outside
    }
    fn setup_membership(&mut self, world: &Puzzle) {
        self.completely_inside = world
            .line
            .iter()
            .filter(|r| r.within_range(&self.center, -3 * (self.radius as isize)))
            .count();
        self.completely_outside = world
            .line
            .iter()
            .filter(|r| !r.within_range(&self.center, 3 * self.radius as isize))
            .count();
    }
    fn is_coherent(&mut self, world: &Puzzle) -> Option<usize> {
        (world.num_robots == self.completely_inside + self.completely_outside)
            .then(|| world.count(&self.center))
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
    fn abs_dist(&self) -> usize {
        self.center.0.unsigned_abs() + self.center.1.unsigned_abs() + self.center.2.unsigned_abs()
    }
    fn dist(&self, other: &Dim3) -> usize {
        unimplemented!()
    }
}

impl PartialOrd for Cubic {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.completely_inside.partial_cmp(&other.completely_inside)
        // self.abs_dist().partial_cmp(&other.abs_dist())
    }
}

impl Ord for Cubic {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.completely_inside.cmp(&other.completely_inside)
        // self.abs_dist().cmp(&other.abs_dist())
    }
}
