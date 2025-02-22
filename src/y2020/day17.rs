//! <https://adventofcode.com/2020/day/17>
use {
    crate::{
        framework::{AdventOfCode, ParseError, aoc},
        geometric::Dim2,
    },
    std::{collections::HashSet, hash::Hash},
};

#[derive(Clone, Debug, Default)]
pub struct Puzzle {
    line: Vec<Vec<bool>>,
    map: HashSet<Dim2<isize>>,
}

#[aoc(2020, 17)]
impl AdventOfCode for Puzzle {
    fn prepare(&mut self, input: &str) -> Result<(), ParseError> {
        self.line = input
            .lines()
            .map(|line| line.chars().map(|c| c == '#').collect::<Vec<_>>())
            .collect();
        let offset_y = ((self.line.len() - 1) / 2) as isize;
        let offset_x = ((self.line[0].len() - 1) / 2) as isize;
        for (y, l) in self.line.iter().enumerate() {
            for (x, b) in l.iter().enumerate() {
                if *b {
                    self.map
                        .insert((y as isize - offset_y, x as isize - offset_x));
                }
            }
        }
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        World::<LOC>::solve(&self.map)
    }
    fn part2(&mut self) -> Self::Output2 {
        World::<LOC4>::solve(&self.map)
    }
}

#[allow(clippy::upper_case_acronyms)]
type LOC = (isize, isize, isize);

#[allow(clippy::upper_case_acronyms)]
type LOC4 = (isize, isize, isize, isize);

#[derive(Clone, Debug, Default, PartialEq)]
struct World<DIM: Eq + Hash> {
    loc: HashSet<DIM>,
    generation: usize,
}

trait CellParser
where
    Self: Sized,
{
    type INDEX;
    fn from_map(map: &HashSet<Dim2<isize>>) -> Self;
    fn neighbors(&self, l: Self::INDEX) -> usize;
    fn next(&mut self) -> Self;
    fn actives(&self) -> usize;
    fn solve(map: &HashSet<Dim2<isize>>) -> usize {
        Self::from_map(map)
            .next()
            .next()
            .next()
            .next()
            .next()
            .next()
            .actives()
    }
}

impl CellParser for World<LOC> {
    type INDEX = LOC;
    fn from_map(map: &HashSet<Dim2<isize>>) -> Self {
        let mut instance = Self::default();
        for (y, x) in map.iter() {
            instance.loc.insert((0, *y, *x));
        }
        instance
    }
    fn neighbors(&self, l: Self::INDEX) -> usize {
        (-1..=1)
            .map(|z| {
                (-1..=1)
                    .map(|y| {
                        (-1..=1)
                            .map(|x| {
                                (((z, y, x) != (0, 0, 0))
                                    && self.loc.contains(&(l.0 + z, l.1 + y, l.2 + x)))
                                    as usize
                            })
                            .sum::<usize>()
                    })
                    .sum::<usize>()
            })
            .sum::<usize>()
    }
    fn next(&mut self) -> Self {
        let mut next = self.clone();
        let mut z_range = (isize::MAX, isize::MIN);
        let mut y_range = (isize::MAX, isize::MIN);
        let mut x_range = (isize::MAX, isize::MIN);
        for (z, y, x) in self.loc.iter() {
            z_range.0 = z_range.0.min(*z - 1);
            z_range.1 = z_range.1.max(*z + 1);
            y_range.0 = y_range.0.min(*y - 1);
            y_range.1 = y_range.1.max(*y + 1);
            x_range.0 = x_range.0.min(*x - 1);
            x_range.1 = x_range.1.max(*x + 1);
        }
        next.loc.clear();
        for z in z_range.0..=z_range.1 {
            for y in y_range.0..=y_range.1 {
                for x in x_range.0..=x_range.1 {
                    let l = (z, y, x);
                    let na = self.neighbors(l);
                    if na == 3 || (self.loc.contains(&l) && na == 2) {
                        next.loc.insert(l);
                    }
                }
            }
        }
        next.generation = self.generation + 1;
        next
    }
    fn actives(&self) -> usize {
        self.loc.len()
    }
}

impl CellParser for World<LOC4> {
    type INDEX = LOC4;
    fn from_map(map: &HashSet<Dim2<isize>>) -> Self {
        let mut instance = Self::default();
        for (y, x) in map.iter() {
            instance.loc.insert((0, 0, *y, *x));
        }
        instance
    }
    fn neighbors(&self, l: Self::INDEX) -> usize {
        (-1..=1)
            .map(|t| {
                (-1..=1)
                    .map(|z| {
                        (-1..=1)
                            .map(|y| {
                                (-1..=1)
                                    .map(|x| {
                                        (((t, z, y, x) != (0, 0, 0, 0))
                                            && self.loc.contains(&(
                                                l.0 + t,
                                                l.1 + z,
                                                l.2 + y,
                                                l.3 + x,
                                            ))) as usize
                                    })
                                    .sum::<usize>()
                            })
                            .sum::<usize>()
                    })
                    .sum::<usize>()
            })
            .sum::<usize>()
    }
    fn next(&mut self) -> Self {
        let mut next = self.clone();
        let mut t_range = (isize::MAX, isize::MIN);
        let mut z_range = (isize::MAX, isize::MIN);
        let mut y_range = (isize::MAX, isize::MIN);
        let mut x_range = (isize::MAX, isize::MIN);
        for (t, z, y, x) in self.loc.iter() {
            t_range.0 = t_range.0.min(*t - 1);
            t_range.1 = t_range.1.max(*t + 1);
            z_range.0 = z_range.0.min(*z - 1);
            z_range.1 = z_range.1.max(*z + 1);
            y_range.0 = y_range.0.min(*y - 1);
            y_range.1 = y_range.1.max(*y + 1);
            x_range.0 = x_range.0.min(*x - 1);
            x_range.1 = x_range.1.max(*x + 1);
        }
        next.loc.clear();
        for t in t_range.0..=t_range.1 {
            for z in z_range.0..=z_range.1 {
                for y in y_range.0..=y_range.1 {
                    for x in x_range.0..=x_range.1 {
                        let l = (t, z, y, x);
                        let na = self.neighbors(l);
                        if na == 3 || (self.loc.contains(&l) && na == 2) {
                            next.loc.insert(l);
                        }
                    }
                }
            }
        }
        next.generation = self.generation + 1;
        next
    }
    fn actives(&self) -> usize {
        self.loc.len()
    }
}
