//! <https://adventofcode.com/2023/day/24>
// #![allow(dead_code)]
// #![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::{Dim2, Dim3},
        line_parser, progress,
    },
    itertools::Itertools,
    std::collections::{HashMap, HashSet},
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<(Dim3<isize>, Dim3<isize>)>,
}

#[aoc(2023, 24)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        // 144788461200241, 195443318499267, 285412990927879 @ 227, 158, 5
        let b = block.split(" @ ").collect::<Vec<&str>>();
        self.line.push((
            {
                let v = line_parser::to_isizes(b[0], '\t').unwrap();
                (v[0], v[1], v[2])
            },
            {
                let v = line_parser::to_isizes(b[1], '\t').unwrap();
                (v[0], v[1], v[2])
            },
        ));
        Ok(())
    }
    fn end_of_data(&mut self) {
        dbg!(self.line.len());
    }
    fn part1(&mut self) -> Self::Output1 {
        const LEAST: f64 = 200000000000000.0;
        const MOST: f64 = 400000000000000.0;
        self.line
            .iter()
            .map(|(p, v)| ((p.0 as f64, p.1 as f64), (v.0 as f64, v.1 as f64)))
            .enumerate()
            .map(|(y, p)| {
                self.line
                    .iter()
                    .map(|(p, v)| ((p.0 as f64, p.1 as f64), (v.0 as f64, v.1 as f64)))
                    .enumerate()
                    .filter(|(x, _)| y < *x)
                    .filter(|(_, q)| {
                        intersect_in_plane(p, *q).map_or(false, |(y, x)| {
                            LEAST <= y && y <= MOST && LEAST <= x && x <= MOST
                        })
                    })
                    .count()
            })
            .sum()
    }
    fn part2(&mut self) -> Self::Output2 {
        let forbiddens = self
            .line
            .iter()
            .map(|(p, v)| v.0)
            .collect::<HashSet<_>>()
            .iter()
            .sorted()
            .cloned()
            .collect::<Vec<_>>();
        let min = self.line.iter().map(|(p, v)| p.0).min().unwrap();
        let max = self.line.iter().map(|(p, v)| p.0).max().unwrap();
        panic!();
        self.sweep(&forbiddens, (min, max));
        println!(
            "lifting pos:{:?}",
            self.line
                .iter()
                .flat_map(|(p, v)| (0 < v.0).then_some(p.0))
                .sorted()
                .rev()
                .take(4)
                .collect::<Vec<_>>()
        );
        println!(
            "lifting pos:{:?}",
            self.line
                .iter()
                .flat_map(|(p, v)| (0 < v.0).then_some(p.0))
                .sorted()
                .take(4)
                .collect::<Vec<_>>()
        );
        println!(
            "lifting vec:{:?}",
            self.line
                .iter()
                .flat_map(|(_, v)| (0 < v.0).then_some(v.0))
                .sorted()
                .rev()
                .take(4)
                .rev()
                .collect::<Vec<_>>()
        );
        println!(
            "falling pos:{:?}",
            self.line
                .iter()
                .flat_map(|(p, v)| (0 > v.0).then_some(p.0))
                .sorted()
                .take(4)
                .collect::<Vec<_>>()
        );
        println!(
            "falling pos:{:?}",
            self.line
                .iter()
                .flat_map(|(p, v)| (0 > v.0).then_some(p.0))
                .sorted()
                .rev()
                .take(4)
                .collect::<Vec<_>>()
        );
        println!(
            "falling vec:{:?}",
            self.line
                .iter()
                .flat_map(|(_, v)| (0 > v.0).then_some(v.0))
                .sorted()
                .take(4)
                .collect::<Vec<_>>()
        );
        let ax = self
            .line
            .iter()
            .enumerate()
            .flat_map(|(i, (p, v))| (v.0 < 0).then_some((p.0, v.0, i)))
            .sorted()
            .last()
            .unwrap();
        let bx = self
            .line
            .iter()
            .enumerate()
            .flat_map(|(i, (p, v))| (v.0 > 0).then_some((p.0, v.0, i)))
            .sorted()
            .last()
            .unwrap();
        // sort on X-axis: it leads a constrain about rock's initial position and velocity. Solve it. Then repeat the same procedure on Y and Z.

        let mut range = 3_000_000_000;
        let mut v = 0;
        while range > 0 {
            range /= 2;
            let l_diff = self.check(v - range);
            let r_diff = self.check(v + range);
            if l_diff.abs() < r_diff.abs() {
                v -= range;
                println!("{:10}< | {:10}/{:10}", range, v, l_diff);
            } else {
                v += range;
                println!("{:10}> | {:10}/{:10}", range, v, r_diff);
            }
        }
        for o in -5..=5 {
            println!("v={}: {}", v + o, self.check(v + o));
        }
        2
    }
}
impl Puzzle {
    fn sweep(&self, forbidden: &[isize], range: (isize, isize)) {
        let mut converge: HashMap<isize, Vec<(usize, isize)>> = HashMap::new();
        let width = range.1 - range.0;
        for test in -50..=50 {
            if test == 0 || forbidden.contains(&test) {
                continue;
            }
            let mut countup: HashMap<isize, usize> = HashMap::new();
            for (x, v) in self.line.iter().map(|(p, v)| (p.0, v.0)) {
                let mut diffs: HashSet<isize> = HashSet::new();
                for t in 1..=dbg!((width / test).abs()) {
                    let diff = x + t * v - t * test;
                    diffs.insert(diff);
                }
                for d in diffs.iter() {
                    *countup.entry(*d).or_default() += 1;
                }
            }
            for (dist, count) in countup.iter() {
                converge.entry(*dist).or_default().push((*count, test));
            }
        }
        for value in converge.values_mut() {
            value.sort();
            value.reverse();
        }
        dbg!(converge.len());
        dbg!(converge
            .iter()
            .map(|(x, l)| (l[0], x))
            .sorted()
            .rev()
            .take(2)
            .collect::<Vec<_>>());
        // for value in converge.values_mut() {
        //     value.sort();
        //     value.reverse();
        // }
        // dbg!(converge.iter().map(|(x, l)| (l[0], x)).max().unwrap());
    }
    fn check(&self, at: isize) -> isize {
        let mut converge: HashMap<isize, Vec<(usize, isize)>> = HashMap::new();
        for test in 0..=0 {
            let mut countup: HashMap<isize, usize> = HashMap::new();
            for (x, v) in self.line.iter().map(|(p, v)| (p.0, v.0)) {
                let mut diffs: HashSet<isize> = HashSet::new();
                for t in 1..2000isize {
                    let diff = x + t * v - t * (test + at);
                    diffs.insert(diff);
                }
                for d in diffs.iter() {
                    *countup.entry(*d).or_default() += 1;
                }
            }
            for (dist, count) in countup.iter() {
                converge.entry(*dist).or_default().push((*count, test + at));
            }
        }
        // for value in converge.values_mut() {
        //     value.sort();
        //     value.reverse();
        // }
        // dbg!(converge.iter().map(|(x, l)| (l[0], x)).max().unwrap());
        return converge.iter().map(|(dist, l)| dist.abs()).min().unwrap();
    }
}

fn intersect_in_plane(a: (Dim2<f64>, Dim2<f64>), b: (Dim2<f64>, Dim2<f64>)) -> Option<Dim2<f64>> {
    let f = b.1 .1 * a.1 .0 - b.1 .0 * a.1 .1;
    let g = a.1 .1 * b.1 .0 - a.1 .0 * b.1 .1;
    if f == 0.0 || g == 0.0 {
        return None;
    }
    let ta = (b.1 .0 * (a.0 .1 - b.0 .1) - b.1 .1 * (a.0 .0 - b.0 .0)) / f;
    let tb = (a.1 .0 * (b.0 .1 - a.0 .1) - a.1 .1 * (b.0 .0 - a.0 .0)) / g;
    if ta < 0.0 || tb < 0.0 {
        return None;
    }
    Some((a.1 .0 * ta + a.0 .0, a.1 .1 * ta + a.0 .1))
    /*
    f = a.1*ta + a.0
    g = b.1*tb + b.0
    a.1*ta + a.0 = b.1*tb + b.0

    a.1.0*ta + a.0.0 = b.1.0*tb + b.0.0
    a.1.1*ta + a.0.1 = b.1.1*tb + b.0.1

    ta = (b.1.0*tb + b.0.0 - a.0.0) / a.1.0
    a.1.1*(b.1.0*tb + b.0.0 - a.0.0) = a.1.0 * (b.1.1*tb + b.0.1 - a.0.1)
    (a.1.1*b.1.0 - a.1.0 * b.1.1) tb = a.1.0 * (b.0.1 - a.0.1) - a.1.1*(b.0.0 - a.0.0)

    tb = (a.1.1*ta + a.0.1 - b.0.1) / b.1.1
    a.1.0*ta + a.0.0 = b.1.0 * (a.1.1*ta + a.0.1 - b.0.1) / b.1.1 + b.0.0
    b.1.1* a.1.0*ta + b.1.1*(a.0.0 - b.0.0) = b.1.0 * a.1.1*ta + b.1.0 * (a.0.1 - b.0.1)
    (b.1.1*a.1.0 - b.1.0*a.1.1)*ta = b.1.0*(a.0.1 - b.0.1) - b.1.1*(a.0.0 - b.0.0)
    */
}
