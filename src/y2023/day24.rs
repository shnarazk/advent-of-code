//! <https://adventofcode.com/2023/day/24>
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::{Dim2, Dim3},
        parser,
    },
    std::collections::{HashMap, HashSet},
};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<(Dim3<isize>, Dim3<isize>)>,
}

#[aoc(2023, 24)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        let b = block.split(" @ ").collect::<Vec<&str>>();
        self.line.push((
            {
                let v = parser::to_isizes(b[0], &[' ', ',']).unwrap();
                (v[0], v[1], v[2])
            },
            {
                let v = parser::to_isizes(b[1], &[' ', ',']).unwrap();
                (v[0], v[1], v[2])
            },
        ));
        Ok(())
    }
    // fn end_of_data(&mut self) { dbg!(self.line.len()); }
    fn serialize(&self) -> Option<String> {
        let vec_x = self
            .line
            .iter()
            .map(|(p, v)| (p.0, v.0))
            .collect::<Vec<_>>();
        serde_json::to_string(&vec_x).ok()
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
                            (LEAST..=MOST).contains(&y) && (LEAST..=MOST).contains(&x)
                        })
                    })
                    .count()
            })
            .sum()
    }
    fn part2(&mut self) -> Self::Output2 {
        let vx = {
            let forbiddens = self.line.iter().map(|(_, v)| v.0).collect::<HashSet<_>>();
            let mut hist: HashMap<isize, usize> = HashMap::new();
            for (i, (p0, v0)) in self.line.iter().enumerate() {
                for (p1, v1) in self.line.iter().skip(i + 1) {
                    if v0.0 != v1.0 {
                        continue;
                    }
                    for s in -400..=400 {
                        if (s - v0.0).abs() != 0
                            && (p1.0 - p0.0) % (s - v0.0) == 0
                            && !forbiddens.contains(&s)
                        {
                            *hist.entry(s).or_default() += 1;
                        }
                    }
                }
            }
            dbg!(*hist.iter().map(|(k, v)| (v, k)).max().unwrap().1)
        };
        let vy = {
            let forbiddens = self.line.iter().map(|(_, v)| v.1).collect::<HashSet<_>>();
            let mut hist: HashMap<isize, usize> = HashMap::new();
            for (i, (p0, v0)) in self.line.iter().enumerate() {
                for (p1, v1) in self.line.iter().skip(i + 1) {
                    if v0.1 != v1.1 {
                        continue;
                    }
                    for s in -400..=400 {
                        if (s - v0.1).abs() != 0
                            && (p1.1 - p0.1) % (s - v0.1) == 0
                            && !forbiddens.contains(&s)
                        {
                            *hist.entry(s).or_default() += 1;
                        }
                    }
                }
            }
            dbg!(*hist.iter().map(|(k, v)| (v, k)).max().unwrap().1)
        };
        let vz = {
            let forbiddens = self.line.iter().map(|(_, v)| v.2).collect::<HashSet<_>>();
            let mut hist: HashMap<isize, usize> = HashMap::new();
            for (i, (p0, v0)) in self.line.iter().enumerate() {
                for (p1, v1) in self.line.iter().skip(i + 1) {
                    if v0.2 != v1.2 {
                        continue;
                    }
                    for s in -400..=400 {
                        if (s - v0.2).abs() != 0
                            && (p1.2 - p0.2) % (s - v0.2) == 0
                            && !forbiddens.contains(&s)
                        {
                            *hist.entry(s).or_default() += 1;
                        }
                    }
                }
            }
            dbg!(*hist.iter().map(|(k, v)| (v, k)).max().unwrap().1)
        };
        let a = self.line[0];
        let b = self.line[1];
        /*
        -(1) cx + at * vx = a.0.0 + a.1.0 * at
        -(2) cy + at * vy = a.0.1 + a.1.1 * at
        -(3) cx + bt * vx = b.0.0 + b.1.0 * bt
        -(4) cy + bt * vy = b.0.1 + b.1.1 * bt

        (1=3) (a.1.0 - vx) * at = b.0.0 - a.0.0 + (b.1.0 - vx) * bt
        (2=4) (a.1.1 - vy) * at = b.0.1 - a.0.1 + (b.1.1 - vy) * bt

        (as formula for at)

        (1=3)' (a.1.0 - vx) * at + a.0.0 - b.0.0 = (b.1.0 - vx) * bt
        (2=4)' (a.1.1 - vy) * at + a.0.1 - b.0.1 = (b.1.1 - vy) * bt

            (b.1.1 - vy) * {(a.1.0 - vx) * at + a.0.0 - b.0.0} = (b.1.0 - vx) * {(a.1.1 - vy) * at + a.0.1 - b.0.1}

            (b.1.1 - vy) * (a.1.0 - vx) * at + (b.1.1 - vy) * (a.0.0 - b.0.0) = (b.1.0 - vx) * (a.1.1 - vy) * at + (b.1.0 - vx) * (a.0.1 - b.0.1)

            (b.1.1 - vy) * (a.1.0 - vx) * at - (b.1.0 - vx) * (a.1.1 - vy) * at = (b.1.0 - vx) * (a.0.1 - b.0.1) - (b.1.1 - vy) * (a.0.0 - b.0.0)
            at = (b.1.0 - vx) * (a.0.1 - b.0.1) - (b.1.1 - vy) * (a.0.0 - b.0.0)
                   / ((b.1.1 - vy) * (a.1.0 - vx) - (b.1.0 - vx) * (a.1.1 - vy))
        */
        let at = ((b.1 .0 - vx) * (a.0 .1 - b.0 .1) - (b.1 .1 - vy) * (a.0 .0 - b.0 .0))
            / ((b.1 .1 - vy) * (a.1 .0 - vx) - (b.1 .0 - vx) * (a.1 .1 - vy));
        dbg!(at);

        let pos_x = (a.0 .0 + a.1 .0 * at) - vx * at;
        let pos_y = (a.0 .1 + a.1 .1 * at) - vy * at;
        let pos_z = (a.0 .2 + a.1 .2 * at) - vz * at;
        (pos_x + pos_y + pos_z) as usize
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
}
