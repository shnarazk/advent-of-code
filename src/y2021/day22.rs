//! <https://adventofcode.com/2021/day/22>
use std::collections::HashSet;
use {
    crate::framework::{AdventOfCode, ParseError, aoc},
    itertools::Itertools,
    std::collections::HashMap,
};

#[derive(Clone, Debug, Default)]
pub struct Puzzle {
    line: Vec<(bool, isize, isize, isize, isize, isize, isize)>,
}

mod parser {
    use {
        crate::parser::parse_isize,
        winnow::{
            ModalResult, Parser,
            ascii::newline,
            combinator::{alt, separated, seq},
        },
    };

    fn parse_line(s: &mut &str) -> ModalResult<(bool, isize, isize, isize, isize, isize, isize)> {
        seq!(
            alt(("on", "off")).map(|s| s == "on"),
            _: " x=", parse_isize,
            _: "..", parse_isize,
            _: ",y=", parse_isize,
            _: "..", parse_isize,
            _: ",z=", parse_isize,
            _: "..", parse_isize
        )
        .parse_next(s)
    }

    #[allow(clippy::type_complexity)]
    pub fn parse(
        s: &mut &str,
    ) -> ModalResult<Vec<(bool, isize, isize, isize, isize, isize, isize)>> {
        separated(1.., parse_line, newline).parse_next(s)
    }
}

#[aoc(2021, 22)]
impl AdventOfCode for Puzzle {
    fn prepare(&mut self, mut input: &str) -> Result<(), ParseError> {
        self.line = parser::parse(&mut input)?;
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        let offset = |p: isize| (p + 50isize) as usize;
        let mut grid: Vec<Vec<Vec<bool>>> = Vec::new();
        for _ in 0..=101 {
            let mut v = Vec::new();
            for _ in 0..=101 {
                let mut w = Vec::new();
                w.resize(101, false);
                v.push(w);
            }
            grid.push(v);
        }
        for (to, x1, x2, y1, y2, z1, z2) in self.line.iter() {
            // print!("{}..{},{}..{},{}..{}", x1, x2, y1, y2, z1, z2);
            // println!(
            //     " - {:?},{:?},{:?}",
            //     50 < *z1 || *z2 < -50,
            //     50 < *y1 || *y2 < -50,
            //     50 < *x1 || *x2 < -50,
            // );
            debug_assert!(x1 <= x2 && y1 <= y2 && z1 <= z2);
            if 50 < *z1 || *z2 < -50 {
                continue;
            }
            for z in (*z1).max(-50)..=(*z2).min(50) {
                if 50 < *y1 || *y2 < -50 {
                    continue;
                }
                for y in (*y1).max(-50)..=(*y2).min(50) {
                    if 50 < *x1 || *x2 < -50 {
                        continue;
                    }
                    for x in (*x1).max(-50)..=(*x2).min(50) {
                        grid[offset(z)][offset(y)][offset(x)] = *to;
                    }
                }
            }
        }
        grid.iter()
            .map(|v| {
                v.iter()
                    .map(|w| w.iter().filter(|b| **b).count())
                    .sum::<usize>()
            })
            .sum()
    }
    fn part2(&mut self) -> Self::Output2 {
        let xs: Vec<isize> = self
            .line
            .iter()
            .flat_map(|(_, x1, x2, _, _, _, _)| vec![*x1, *x2 + 1])
            .collect::<HashSet<isize>>()
            .iter()
            .copied()
            .sorted()
            .collect::<Vec<isize>>();
        let ys: Vec<isize> = self
            .line
            .iter()
            .flat_map(|(_, _, _, y1, y2, _, _)| vec![*y1, *y2 + 1])
            .collect::<HashSet<isize>>()
            .iter()
            .copied()
            .sorted()
            .collect::<Vec<isize>>();
        let zs: Vec<isize> = self
            .line
            .iter()
            .flat_map(|(_, _, _, _, _, z1, z2)| vec![*z1, *z2 + 1])
            .collect::<HashSet<isize>>()
            .iter()
            .copied()
            .sorted()
            .collect::<Vec<isize>>();
        let to_index_x: HashMap<isize, usize> = xs
            .iter()
            .enumerate()
            .map(|(i, x)| (*x, i))
            .collect::<HashMap<isize, usize>>();
        let to_index_y: HashMap<isize, usize> = ys
            .iter()
            .enumerate()
            .map(|(i, y)| (*y, i))
            .collect::<HashMap<isize, usize>>();
        let to_index_z: HashMap<isize, usize> = zs
            .iter()
            .enumerate()
            .map(|(i, z)| (*z, i))
            .collect::<HashMap<isize, usize>>();
        let mut grid: Vec<Vec<Vec<bool>>> = zs
            .iter()
            .map(|_| {
                ys.iter()
                    .map(|_| xs.iter().map(|_| false).collect::<Vec<_>>())
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();

        for (to, x1, x2, y1, y2, z1, z2) in self.line.iter() {
            let i1 = *to_index_z.get(z1).unwrap();
            let i2 = *to_index_z.get(&(*z2 + 1)).unwrap();
            let j1 = *to_index_y.get(y1).unwrap();
            let j2 = *to_index_y.get(&(*y2 + 1)).unwrap();
            let k1 = *to_index_x.get(x1).unwrap();
            let k2 = *to_index_x.get(&(*x2 + 1)).unwrap();
            for zz in grid.iter_mut().take(i2).skip(i1) {
                for yy in zz.iter_mut().take(j2).skip(j1) {
                    for xx in yy.iter_mut().take(k2).skip(k1) {
                        *xx = *to;
                    }
                }
            }
        }
        let mut sum = 0;
        for (i, c) in grid.iter().enumerate() {
            for (j, l) in c.iter().enumerate() {
                for (k, b) in l.iter().enumerate() {
                    if *b {
                        sum += (zs[i + 1] - zs[i]) * (ys[j + 1] - ys[j]) * (xs[k + 1] - xs[k]);
                    }
                }
            }
        }
        sum as usize
    }
}
