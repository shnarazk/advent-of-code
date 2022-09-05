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
        let mut max_value = 200;
        let mut max_position = (0, 0, 0);
        let mut best_distance = 0;
        to_visit.push(Reverse(start));
        let mut out = 0;
        let mut rin = 1;
        while let Some(Reverse(mut p)) = to_visit.pop() {
            out += 1;
            if p.affecting() < max_value
            // || (p.affecting(self) == max_value && best_distance < p.closest().abs_dist())
            {
                continue;
            }
            if let Some(n) = p.is_coherent(self) {
                // if 0 < n && 0 < p.radius {
                //     dbg!(n, p.radius);
                // }
                match max_value.cmp(&n) {
                    std::cmp::Ordering::Less => {
                        max_value = n;
                        (best_distance, max_position) = p.closest();
                        dbg!(max_value, best_distance);
                    }
                    std::cmp::Ordering::Equal => {
                        let (d, p) = p.closest();
                        if d < max_position.abs_dist() {
                            max_position = p;
                            best_distance = d;
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
            if 0 == p.radius {
                dbg!(p);
                panic!();
            }
            assert!(0 < p.radius);
            for sub in p.divide(self).iter() {
                // if 2 < q.affecting {
                //     println!("{:?}, {}", q.center, q.max_bound());
                // }
                // record_list.push(q.center);
                to_visit.push(Reverse(sub.clone()));
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
    fn affecting(&self) -> usize {
        1000 - self.completely_outside
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
        assert!(
            0 < self.radius || self.completely_inside + self.completely_outside == world.num_robots
        );
    }
    fn is_coherent(&mut self, world: &Puzzle) -> Option<usize> {
        (world.num_robots == self.completely_inside + self.completely_outside).then(
            || self.completely_inside, // world.count(&self.center
        )
    }
    fn divide(&self, world: &Puzzle) -> Vec<Cubic> {
        let c = self.center;
        let mut vec = if self.radius == 1 {
            vec![
                Cubic {
                    center: c,
                    ..Cubic::default()
                },
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
            ]
        } else {
            let r = (self.radius / 2) as isize;
            let radius = self.radius / 2;
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
        };
        for c in vec.iter_mut() {
            c.setup_membership(world);
        }
        vec
    }
    fn closest(&self) -> (usize, Dim3) {
        const DIRS: [Dim3; 8] = [
            (-1, -1, -1),
            (-1, -1, 1),
            (-1, 1, -1),
            (-1, 1, 1),
            (1, -1, -1),
            (1, -1, 1),
            (1, 1, -1),
            (1, 1, 1),
        ];

        if self.radius == 0 {
            (self.center.abs_dist(), self.center)
        } else {
            DIRS.iter()
                .map(|d| {
                    (
                        self.center.0 + d.0 * self.radius as isize,
                        self.center.1 + d.1 * self.radius as isize,
                        self.center.2 + d.2 * self.radius as isize,
                    )
                })
                .map(|p| (p.abs_dist(), p))
                .min()
                .unwrap()
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
        self.affecting().partial_cmp(&other.affecting())
        // self.abs_dist().partial_cmp(&other.abs_dist())
    }
}

impl Ord for Cubic {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.affecting().cmp(&other.affecting())
        // self.abs_dist().cmp(&other.abs_dist())
    }
}
