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
    radius: usize,
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
        self.radius = self
            .line
            .iter()
            .map(|((x, y, z), _)| x.unsigned_abs().max(y.unsigned_abs()).max(z.unsigned_abs()))
            .max()
            .unwrap()
            .next_power_of_two();
        dbg!(self.num_robots, self.radius);
    }
    fn part1(&mut self) -> Self::Output1 {
        let strongest: (&usize, &Dim3) = self.line.iter().map(|(p, r)| (r, p)).max().unwrap();
        self.line
            .iter()
            .filter(|(p, r)| strongest.1.dist(p) <= *strongest.0)
            .count()
    }
    fn part2(&mut self) -> Self::Output2 {
        let trace = dbg!((15732653, 37370828, 40027284));
        let mut to_visit = BinaryHeap::from([Reverse(Cubic::new(self.radius, self))]);
        let (mut max_count, mut best) = (972, (0, (0, 0, 0)));
        while let Some(Reverse(mut p)) = to_visit.pop() {
            // if p.includes(&trace) {
            //     dbg!(p.radius, p.is_coherent(self));
            // }
            let (target, a) = (p.closest(), p.affecting(self));
            // if max_count == 973 && p.radius == 0 {
            //     dbg!(&p);
            // }
            if a < max_count || a == max_count && best.0 < target.0 {
                // if p.includes(&trace) && p.radius < 2 {
                //     dbg!(p.radius, p.is_coherent(self));
                // }
                continue;
            }
            let coherent = p.is_coherent(self);
            let n = coherent.unwrap_or_else(|| self.count(&p.center));
            match max_count.cmp(&n) {
                std::cmp::Ordering::Less => {
                    // if p.includes(&trace) {
                    //     dbg!(p.radius);
                    // }
                    // dbg!(&coherent, p.radius);
                    max_count = dbg!(n);
                    best = dbg!(target);
                }
                std::cmp::Ordering::Equal if target.0 < best.0 => {
                    // if p.includes(&trace) {
                    //     dbg!(p.radius);
                    // }
                    best = target;
                }
                _ => (),
            }
            if coherent.is_none() {
                let mut vec = p.divide(self);
                if p.includes(&trace) && p.radius == 1 {
                    dbg!(&p);
                }
                while let Some(sub) = vec.pop() {
                    if p.includes(&trace) && p.radius == 1 && sub.center == trace {
                        dbg!(&sub);
                    }
                    to_visit.push(Reverse(sub));
                }
            }
        }
        for x in 0..100_isize {
            for y in 0..100_isize {
                for z in 0..100_isize {
                    let p = (best.1 .0 - x, best.1 .1 - y, best.1 .2 - z);
                    if p != best.1 && max_count < self.count(&p) {
                        dbg!(p);
                    }
                }
            }
        }
        best.0
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
    inside: usize,
    outside: usize,
}

impl Cubic {
    fn includes(&self, pos: &Dim3) -> bool {
        self.center.0 - self.radius as isize <= pos.0
            && pos.0 <= self.center.0 + self.radius as isize
            && self.center.1 - self.radius as isize <= pos.1
            && pos.1 <= self.center.1 + self.radius as isize
            && self.center.2 - self.radius as isize <= pos.2
            && pos.2 <= self.center.2 + self.radius as isize
    }
    fn new(radius: usize, world: &Puzzle) -> Cubic {
        let mut inst = Cubic {
            radius: world.radius,
            ..Cubic::default()
        };
        inst.setup_membership(world);
        inst
    }
    fn affecting(&self, world: &Puzzle) -> usize {
        world.num_robots - self.outside
    }
    fn uncernty(&self) -> usize {
        1000 - self.outside - self.inside
    }
    fn setup_membership(&mut self, world: &Puzzle) {
        self.inside = world
            .line
            .iter()
            .filter(|r| r.within_range(&self.center, -3 * (self.radius as isize)))
            .count();
        self.outside = world
            .line
            .iter()
            .filter(|r| !r.within_range(&self.center, 3 * self.radius as isize))
            .count();
        assert!(0 < self.radius || self.inside + self.outside == world.num_robots);
    }
    fn is_coherent(&mut self, world: &Puzzle) -> Option<usize> {
        (world.num_robots == self.inside + self.outside).then(|| self.inside)
    }
    fn divide(&self, world: &Puzzle) -> Vec<Cubic> {
        let c = self.center;
        let mut vec = if self.radius == 1 {
            [-1, 0, 1]
                .iter()
                .flat_map(|x| {
                    [-1, 0, 1]
                        .iter()
                        .flat_map(|y| {
                            [-1, 0, 1]
                                .iter()
                                .map(|z| Cubic {
                                    center: (c.0 + x, c.1 + y, c.2 + z),
                                    ..Cubic::default()
                                })
                                .collect::<Vec<_>>()
                        })
                        .collect::<Vec<_>>()
                })
                .collect::<Vec<_>>()
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
                    center: (c.0 - r, c.1 - r, c.2 + r),
                    radius,
                    ..Cubic::default()
                },
                Cubic {
                    center: (c.0 - r, c.1 + r, c.2 - r),
                    radius,
                    ..Cubic::default()
                },
                Cubic {
                    center: (c.0 - r, c.1 + r, c.2 + r),
                    radius,
                    ..Cubic::default()
                },
                Cubic {
                    center: (c.0 + r, c.1 - r, c.2 - r),
                    radius,
                    ..Cubic::default()
                },
                Cubic {
                    center: (c.0 + r, c.1 - r, c.2 + r),
                    radius,
                    ..Cubic::default()
                },
                Cubic {
                    center: (c.0 + r, c.1 + r, c.2 - r),
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
            let r = self.radius as isize;
            let zero_x = (self.center.0 - r) * (self.center.0 + r) < 0;
            let zero_y = (self.center.1 - r) * (self.center.1 + r) < 0;
            let zero_z = (self.center.2 - r) * (self.center.2 + r) < 0;
            DIRS.iter()
                .map(|d| {
                    let p = (
                        if zero_x { 0 } else { self.center.0 + d.0 * r },
                        if zero_y { 0 } else { self.center.1 + d.1 * r },
                        if zero_z { 0 } else { self.center.2 + d.2 * r },
                    );
                    (p.abs_dist(), p)
                })
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
        self.uncernty().partial_cmp(&other.uncernty())
        // self.abs_dist().partial_cmp(&other.abs_dist())
    }
}

impl Ord for Cubic {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.uncernty().cmp(&other.uncernty())
        // self.abs_dist().cmp(&other.abs_dist())
    }
}
