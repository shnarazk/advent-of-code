//! <https://adventofcode.com/2021/day/22>
use std::collections::HashSet;
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        line_parser, regex,
    },
    std::collections::HashMap,
};

#[derive(Debug, Default)]
pub struct Puzzle {
    line: Vec<(bool, isize, isize, isize, isize, isize, isize)>,
}

#[aoc(2021, 22)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";

    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        let parser = regex!(
            r"^(on|off) x=(-?[0-9]+)\.\.(-?[0-9]+),y=(-?[0-9]+)\.\.(-?[0-9]+),z=(-?[0-9]+)\.\.(-?[0-9]+)$"
        );
        let segment = parser.captures(block).ok_or(ParseError)?;
        self.line.push((
            &segment[1] == "on",
            line_parser::to_isize(&segment[2])?,
            line_parser::to_isize(&segment[3])?,
            line_parser::to_isize(&segment[4])?,
            line_parser::to_isize(&segment[5])?,
            line_parser::to_isize(&segment[6])?,
            line_parser::to_isize(&segment[7])?,
        ));
        Ok(())
    }
    fn wrap_up(&mut self) {
        dbg!(self
            .line
            .iter()
            .map(|(_, x, _, y, _, z, _)| x.min(y).min(z))
            .min()
            .unwrap());
        dbg!(self
            .line
            .iter()
            .map(|(_, _, x, _, y, _, z)| x.max(y).max(z))
            .max()
            .unwrap());
        // dbg!(&self.line);
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
            print!("{}..{},{}..{},{}..{}", x1, x2, y1, y2, z1, z2);
            println!(
                " - {:?},{:?},{:?}",
                50 < *z1 || *z2 < -50,
                50 < *y1 || *y2 < -50,
                50 < *x1 || *x2 < -50,
            );
            assert!(x1 <= x2 && y1 <= y2 && z1 <= z2);
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
        let mut xs: Vec<isize> = self
            .line
            .iter()
            .flat_map(|(_, x1, x2, _, _, _, _)| vec![*x1, *x2 + 1])
            .collect();
        let mut ys: Vec<isize> = self
            .line
            .iter()
            .flat_map(|(_, _, _, y1, y2, _, _)| vec![*y1, *y2 + 1])
            .collect();
        let mut zs: Vec<isize> = self
            .line
            .iter()
            .flat_map(|(_, _, _, _, _, z1, z2)| vec![*z1, *z2 + 1])
            .collect();

        let mut hx: HashSet<isize> = HashSet::new();
        for x in xs.iter() {
            hx.insert(*x);
        }
        xs = hx.iter().copied().collect::<Vec<_>>();
        let mut hy: HashSet<isize> = HashSet::new();
        for y in ys.iter() {
            hy.insert(*y);
        }
        ys = hy.iter().copied().collect::<Vec<_>>();
        let mut hz: HashSet<isize> = HashSet::new();
        for z in zs.iter() {
            hz.insert(*z);
        }
        zs = hz.iter().copied().collect::<Vec<_>>();

        xs.sort_unstable();
        ys.sort_unstable();
        zs.sort_unstable();
        debug_assert!(xs.windows(2).all(|a| a[0] != a[1]));
        debug_assert!(ys.windows(2).all(|a| a[0] != a[1]));
        debug_assert!(zs.windows(2).all(|a| a[0] != a[1]));
        dbg!(xs.len(), ys.len(), zs.len());
        dbg!(&xs[1..20]);
        let mut to_index_x: HashMap<isize, usize> = HashMap::new();
        let mut to_index_y: HashMap<isize, usize> = HashMap::new();
        let mut to_index_z: HashMap<isize, usize> = HashMap::new();
        for (i, x) in xs.iter().enumerate() {
            to_index_x.insert(*x, i);
        }
        for (i, y) in ys.iter().enumerate() {
            to_index_y.insert(*y, i);
        }
        for (i, z) in zs.iter().enumerate() {
            to_index_z.insert(*z, i);
        }
        let mut grid: Vec<Vec<Vec<bool>>> = Vec::new();
        for _ in 0..zs.len() {
            let mut w: Vec<Vec<bool>> = Vec::new();
            for _ in 0..ys.len() {
                let mut v: Vec<bool> = Vec::new();
                v.resize(xs.len(), false);
                w.push(v);
            }
            grid.push(w);
        }

        for (to, x1, x2, y1, y2, z1, z2) in self.line.iter() {
            for k in grid
                .iter_mut()
                .take(*to_index_z.get(&(*z2 + 1)).unwrap())
                .skip(*to_index_z.get(z1).unwrap())
            {
                for l in k
                    .iter_mut()
                    .take(*to_index_y.get(&(*y2 + 1)).unwrap())
                    .skip(*to_index_y.get(y1).unwrap())
                {
                    for m in l
                        .iter_mut()
                        .take(*to_index_x.get(&(*x2 + 1)).unwrap())
                        .skip(*to_index_x.get(x1).unwrap())
                    {
                        *m = *to;
                    }
                }
            }
        }
        zs.windows(2)
            .map(|pz| {
                ys.windows(2)
                    .map(|py| {
                        xs.windows(2)
                            .map(|px| {
                                if grid[*to_index_z.get(&pz[0]).unwrap()]
                                    [*to_index_y.get(&py[0]).unwrap()]
                                    [*to_index_x.get(&px[0]).unwrap()]
                                {
                                    ((pz[1] - pz[0]) * (py[1] - py[0]) * (px[1] - px[0])) as usize
                                } else {
                                    0
                                }
                            })
                            .sum::<usize>()
                    })
                    .sum::<usize>()
            })
            .sum()
    }
}
