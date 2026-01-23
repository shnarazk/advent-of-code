//! <https://adventofcode.com/2025/day/9>
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::{Dim2, NeighborIter},
    },
    // rayon::prelude::*,
    rustc_data_structures::fx::{FxHashMap, FxHasher},
    std::{
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
            ascii::newline,
            combinator::{separated, seq},
            ModalResult, Parser,
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
            // assert_eq!(pair.len(), 2);
            pair.sort();
        });
        slice_x.iter_mut().for_each(|(_, pair)| {
            // assert_eq!(pair.len(), 2);
            pair.sort();
        });

        let grid_size = ys.len() + 2;
        let mut grid = vec![vec![3; grid_size]; grid_size];
        for (y, xs) in slice_y.iter() {
            grid[encode_y[y]][encode_x[&xs[0]]] = 1;
            grid[encode_y[y]][encode_x[&xs[1]]] = 1;
            for x in grid[encode_y[y]]
                .iter_mut()
                .take(encode_x[&xs[1]])
                .skip(encode_x[&xs[0]] + 1)
            {
                *x = 2;
            }
        }
        for (x, ys) in slice_x.iter() {
            // grid[encode_y[&ys[0]]][encode_x[x]] = 1;
            // grid[encode_y[&ys[1]]][encode_x[x]] = 1;
            for l in grid
                .iter_mut()
                .take(encode_y[&ys[1]])
                .skip(encode_y[&ys[0]] + 1)
            {
                l[encode_x[x]] = 2;
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
        for by in 1..grid_size {
            for bx in 1..grid_size {
                if grid[by][bx] != 1 {
                    continue;
                }
                let mut min_x = 0;
                for y in by..grid_size {
                    for x in (min_x..=bx).rev() {
                        if grid[y][x] == 0 {
                            min_x = x + 1;
                            break;
                        }
                        if grid[y][x] == 1 {
                            let a = (ys[by].abs_diff(ys[y]) + 1) * (xs[bx].abs_diff(xs[x]) + 1);
                            area = area.max(a);
                        }
                    }
                }
                let mut max_x = grid_size;
                for y in by..grid_size {
                    for x in bx..max_x {
                        if grid[y][x] == 0 {
                            max_x = x;
                            break;
                        }
                        if grid[y][x] == 1 {
                            let a = (ys[by].abs_diff(ys[y]) + 1) * (xs[bx].abs_diff(xs[x]) + 1);
                            area = area.max(a);
                        }
                    }
                }
            }
        }
        area
    }
}
