//! <https://adventofcode.com/2023/day/24>
// #![allow(dead_code)]
// #![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::{Dim2, Dim3},
        line_parser,
    },
    itertools::Itertools,
};

// std::collections::HashMap,

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
        // println!(
        //     "{:?}",
        //     self.line
        //         .iter()
        //         .map(|(p, v)| (p.0, v.0))
        //         .sorted()
        //         .take(100)
        //         .collect::<Vec<_>>()
        // );
        // sort on X-axis: it leads a constrain about rock's initial position and velocity. Solve it. Then repeat the same procedure on Y and Z.
        2
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
