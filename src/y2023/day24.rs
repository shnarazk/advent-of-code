//! <https://adventofcode.com/2023/day/24>
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::{Dim2, Dim3},
        line_parser,
    },
    std::collections::HashSet,
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
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
    // fn end_of_data(&mut self) { dbg!(self.line.len()); }
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
        let forbiddens = self.line.iter().map(|(_, v)| v.0).collect::<HashSet<_>>();
        dbg!(self.line.len() - forbiddens.len());
        let forbiddens = self.line.iter().map(|(_, v)| v.0).collect::<HashSet<_>>();
        for (i, (p0, v0)) in self.line.iter().enumerate() {
            for (_, (p1, v1)) in self.line.iter().enumerate().skip(i) {
                if v0.0 != v1.0 {
                    continue;
                }
                for s in -400..=400 {
                    if s == v0.0 {
                        continue;
                    }
                    let m = (p1.0 - p0.0) % (s - v0.0);
                    if m == 0 {
                        dbg!(s);
                    }
                }
            }
        }
        return 0;
        'next_speed: for s in -400..=400 {
            if forbiddens.contains(&s) {
                continue;
            }
            // if s != -356 { continue; }
            let mut mods: HashSet<isize> = HashSet::new();
            // for (p, v) in self.line.iter() {
            //     if s - v.0 == 0 {
            //         continue 'next_speed;
            //     }
            //     let m = p.0 % (s - v.0);
            //     mods.insert(m);
            // }
            for (p, v) in self.line.iter() {
                for (q, w) in self.line.iter() {
                    // if v.0 == w.0 {
                    let m = (q.0 - p.0) % (s + v.0);
                    mods.insert(m);
                }
                let m = p.0 % (s - v.0);
                mods.insert(m);
            }
            dbg!(mods.len());
            if mods.len() <= 6 {
                return dbg!(s as usize);
            }
        }
        0
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
