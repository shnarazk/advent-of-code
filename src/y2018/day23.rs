//! <https://adventofcode.com/2018/day/23>
use {
    crate::{
        color,
        framework::{aoc, AdventOfCode, ParseError},
        regex,
    },
    std::{cmp::Reverse, collections::BinaryHeap},
};

type Dim3 = (isize, isize, isize);

trait Geometry {
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
    fn end_of_data(&mut self) {
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
            .filter(|(p, _)| strongest.1.dist(p) <= *strongest.0)
            .count()
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut to_visit = BinaryHeap::from([Reverse(Cubic::new(self.radius, self))]);
        let (mut max_count, mut best) = {
            let p: (&usize, &Dim3) = self.line.iter().map(|(p, r)| (r, p)).max().unwrap();
            (self.count(p.1), (p.1.abs_dist(), *p.1))
        };
        let mut terminals: BinaryHeap<Reverse<Cubic>> = BinaryHeap::new();
        println!();
        while let Some(Reverse(mut p)) = terminals.pop().or_else(|| to_visit.pop()) {
            let (target, a) = (p.closest(), p.affecting(self));
            if a < max_count || a == max_count && best.0 < target.0 {
                continue;
            }
            let coherent = p.is_coherent(self);
            let n = coherent.unwrap_or_else(|| self.count(&p.center));
            match max_count.cmp(&n) {
                std::cmp::Ordering::Less => {
                    max_count = n;
                    best = target;
                    println!("{}n = {}, d = {}", color::REVERT, n, best.0);
                }
                std::cmp::Ordering::Equal if target.0 < best.0 => {
                    best = target;
                    println!("{}n = {}, d = {}", color::REVERT, n, best.0);
                }
                _ => (),
            }
            if coherent.is_none() {
                let mut vec = p.divide(self);
                while let Some(sub) = vec.pop() {
                    if sub.radius == 0 {
                        terminals.push(Reverse(sub));
                    } else {
                        to_visit.push(Reverse(sub));
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
    #[allow(dead_code)]
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
            radius,
            ..Cubic::default()
        };
        inst.setup_membership(world);
        inst
    }
    fn affecting(&self, world: &Puzzle) -> usize {
        world.num_robots - self.outside
    }
    fn affecting_(&self) -> isize {
        -(self.outside as isize)
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
        (world.num_robots == self.inside + self.outside).then_some(self.inside)
    }
    fn divide(&self, world: &Puzzle) -> Vec<Cubic> {
        let c = self.center;
        let mut vec = if self.radius == 1 {
            let dirs = [-1, 0, 1]
                .iter()
                .flat_map(|x| {
                    [-1, 0, 1]
                        .iter()
                        .flat_map(|y| [-1, 0, 1].iter().map(|z| (*x, *y, *z)).collect::<Vec<_>>())
                        .collect::<Vec<_>>()
                })
                .collect::<Vec<_>>();
            dirs.iter()
                .filter(|d| **d != (0, 0, 0))
                .map(|d| Cubic {
                    center: (c.0 + d.0, c.1 + d.1, c.2 + d.2),
                    ..Cubic::default()
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
    fn dist(&self, _other: &Dim3) -> usize {
        unimplemented!()
    }
}

impl PartialOrd for Cubic {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Cubic {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.affecting_().cmp(&other.affecting_())
    }
}
