//! <https://adventofcode.com/2025/day/9>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{AdventOfCode, ParseError, aoc},
        geometric::{Dim2, NeighborIter},
    },
    // rayon::prelude::*,
    rustc_data_structures::fx::{FxHashMap, FxHasher},
    // serde::Serialize,
    std::{
        cmp::{Ordering, Reverse},
        collections::{HashMap, HashSet},
        hash::BuildHasherDefault,
    },
};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Dim2<usize>>,
}

mod parser {
    use {
        crate::{geometric::Dim2, parser::parse_usize},
        winnow::{
            ModalResult, Parser,
            ascii::{alpha1, newline, space1},
            combinator::{alt, separated, seq},
        },
    };

    fn parse_line(s: &mut &str) -> ModalResult<Dim2<usize>> {
        seq!(parse_usize, _: ",", parse_usize)
            .map(|(x, y)| (y, x))
            .parse_next(s)
    }
    pub fn parse(s: &mut &str) -> ModalResult<Vec<Dim2<usize>>> {
        separated(1.., parse_line, newline).parse_next(s)
    }
}

#[aoc(2025, 9)]
impl AdventOfCode for Puzzle {
    fn prepare(&mut self, mut input: &str) -> Result<(), ParseError> {
        self.line = parser::parse(&mut input)?;
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        self.line
            .iter()
            .enumerate()
            .map(|(i, p)| {
                self.line
                    .iter()
                    .skip(i)
                    .map(|q| (p.0.abs_diff(q.0) + 1) * (p.1.abs_diff(q.1) + 1))
                    .max()
                    .expect("!")
            })
            .max()
            .unwrap()
    }
    fn part2(&mut self) -> Self::Output2 {
        assert!(self.line.iter().all(|p| p.0 > 0 && p.1 > 0));
        let mut ys = self
            .line
            .iter()
            .map(|p| p.0)
            .collect::<HashSet<_>>()
            .into_iter()
            .collect::<Vec<_>>();
        ys.push(0);
        ys.sort();
        let encode_y = ys
            .iter()
            .enumerate()
            .map(|(e, d)| (*d, e))
            .collect::<HashMap<_, _>>();
        let mut xs = self
            .line
            .iter()
            .map(|p| p.1)
            .collect::<HashSet<_>>()
            .into_iter()
            .collect::<Vec<_>>();
        xs.push(0);
        xs.sort();
        let encode_x = xs
            .iter()
            .enumerate()
            .map(|(e, d)| (*d, e))
            .collect::<HashMap<_, _>>();
        let mut slice_y: FxHashMap<usize, Vec<usize>> =
            HashMap::<_, _, BuildHasherDefault<FxHasher>>::default();
        let mut slice_x: FxHashMap<usize, Vec<usize>> =
            HashMap::<_, _, BuildHasherDefault<FxHasher>>::default();
        for p in self.line.iter() {
            slice_y.entry(p.0).or_default().push(p.1);
            slice_x.entry(p.1).or_default().push(p.0);
        }

        slice_y.iter_mut().for_each(|(_, pair)| {
            assert_eq!(pair.len(), 2);
            pair.sort();
        });
        slice_x.iter_mut().for_each(|(_, pair)| {
            assert_eq!(pair.len(), 2);
            pair.sort();
        });
        let grid_size = ys.len() + 2;
        let mut grid = vec![vec![3; grid_size]; grid_size];
        for (y, xs) in slice_y.iter() {
            grid[encode_y[y]][encode_x[&xs[0]]] = 1;
            grid[encode_y[y]][encode_x[&xs[1]]] = 1;
            for x in encode_x[&xs[0]] + 1..encode_x[&xs[1]] {
                grid[encode_y[y]][x] = 2;
            }
        }
        for (x, ys) in slice_x.iter() {
            grid[encode_y[&ys[0]]][encode_x[x]] = 1;
            grid[encode_y[&ys[1]]][encode_x[x]] = 1;
            for y in encode_y[&ys[0]] + 1..encode_y[&ys[1]] {
                grid[y][encode_x[x]] = 2;
            }
        }
        let mut to_visit: Vec<Dim2<usize>> = vec![(0, 0)];
        while let Some(p) = to_visit.pop() {
            if grid[p.0][p.1] == 3 {
                grid[p.0][p.1] = 0;
                for q in p.iter8(&(grid_size, grid_size)) {
                    if grid[q.0][q.1] == 3 {
                        to_visit.push(q);
                    }
                }
            }
        }
        for l in grid.iter_mut() {
            for k in l.iter_mut() {
                if *k == 3 {
                    *k = 2;
                }
            }
        }

        let mut area = 0;
        for gy in 1..grid_size {
            for gx in 1..grid_size {
                if grid[gy][gx] == 0 {
                    continue;
                }
                let mut max_x = grid_size;
                for y in gy..grid_size {
                    for x in gx..max_x {
                        if grid[y][x] == 0 {
                            max_x = x;
                            break;
                        }
                        if (grid[gy][gx] == 1 && grid[y][x] == 1)
                            || (grid[gy][x] == 1 && grid[y][gx] == 1)
                        {
                            let a = (ys[gy].abs_diff(ys[y]) + 1) * (xs[gx].abs_diff(xs[x]) + 1);
                            area = area.max(a);
                        }
                    }
                }
            }
        }
        return area;
        // ここまでOK
        self.line.sort();
        for (i, p) in self.line.iter().enumerate() {
            'next: for q in self.line.iter().skip(i) {
                let flag = *p == (3, 2) && *q == (5, 9);
                if flag {
                    dbg!(q);
                }
                // 交差する線分があってはいけない
                for (y, xs) in slice_y.iter() {
                    if p.0 < *y && *y < q.0 && (xs[0] < q.1 && p.1 < xs[1]) {
                        continue 'next;
                    }
                }
                for (x, ys) in slice_x.iter() {
                    if p.1 < *x && *x < q.1 && (ys[0] < q.0 && p.0 < ys[1]) {
                        continue 'next;
                    }
                }
                for r in self.line.iter() {
                    if p.0 < r.0 && p.1 < r.1 && r.0 < q.0 && r.1 < q.1 {
                        if flag {
                            dbg!();
                        }
                        continue 'next;
                    }
                }
                // TODO: もう一つの条件は逆対角線を作る2点がどこかの線分上に存在すること
                let target1 = (p.0, q.1);
                let target2 = (q.0, p.1);
                let slice1 = slice_y.get(&p.0).unwrap();
                if !(slice1[0] <= target1.1 && target1.1 <= slice1[1]) {
                    let inside = slice_x
                        .iter()
                        .filter(|(a, b)| b[0] < target1.0 && target1.0 < b[1])
                        .count()
                        % 2;
                    if flag {
                        dbg!(target1);
                    }
                    if inside == 0 {
                        continue;
                    }
                }
                let slice2 = slice_y.get(&q.0).unwrap();
                if !(slice2[0] <= target2.1 && target2.1 <= slice2[1]) {
                    let inside = slice_x
                        .iter()
                        .filter(|(a, b)| b[0] < target2.0 && target2.0 < b[1])
                        .count()
                        % 2;
                    if flag {
                        dbg!();
                    }
                    if inside == 0 {
                        continue;
                    }
                }
                let a = (p.0.abs_diff(q.0) + 1) * (p.1.abs_diff(q.1) + 1);
                // if a > area {
                //     println!("{p:?}, {q:?} => {a}");
                // }
                area = area.max(a);
            }
        }
        area
    }
}
// too high: 3053207276
// too high: 2695024914
