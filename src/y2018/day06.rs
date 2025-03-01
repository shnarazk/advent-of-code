//! <https://adventofcode.com/2018/day/6>
use {
    crate::{
        framework::{AdventOfCode, ParseError, aoc},
        parser,
    },
    std::collections::{HashMap, HashSet},
};

macro_rules! mdist {
    ($a: expr, $b: expr) => {{ $a.0.abs_diff($b.0) + $a.1.abs_diff($b.1) }};
}

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<(usize, usize)>,
}

#[aoc(2018, 6)]
impl AdventOfCode for Puzzle {
    fn prepare(&mut self, input: &str) -> Result<(), ParseError> {
        for l in input.lines() {
            let v = parser::to_usizes(l, &[' ', ','])?;
            self.line.push((v[1], v[0]));
        }
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        let min_y = self.line.iter().map(|(y, _)| *y).min().expect("strange");
        let max_y = self.line.iter().map(|(y, _)| *y).max().expect("strange");
        let min_x = self.line.iter().map(|(_, x)| *x).min().expect("strange");
        let max_x = self.line.iter().map(|(_, x)| *x).max().expect("strange");
        debug_assert!(10 < min_y && 10 < min_x);
        let offset: usize = 10;
        let mut infinite_ids: HashSet<usize> = HashSet::new();
        // top edge and bottom edge
        for x in (min_x - offset)..(max_x + offset) {
            for y in [min_y, max_y] {
                for id in self.shortest_to((y, x)).1 {
                    infinite_ids.insert(id);
                }
            }
        }
        // left edge and right edge
        for y in (min_y - offset)..(max_y + offset) {
            for x in [min_x, max_x] {
                for id in self.shortest_to((y, x)).1 {
                    infinite_ids.insert(id);
                }
            }
        }
        // let's draw the picture
        let mut count: HashMap<usize, usize> = HashMap::new();
        for y in min_y..=max_y {
            for x in min_x..=max_x {
                let ids = self.shortest_to((y, x)).1;
                if ids.len() == 1 && !infinite_ids.contains(&ids[0]) {
                    *count.entry(ids[0]).or_insert(0) += 1;
                }
            }
        }
        *count.values().max().unwrap_or(&0)
    }
    fn part2(&mut self) -> Self::Output2 {
        let limit = 10000;
        let min_y = self.line.iter().map(|(y, _)| *y).min().expect("strange");
        let max_y = self.line.iter().map(|(y, _)| *y).max().expect("strange");
        let min_x = self.line.iter().map(|(_, x)| *x).min().expect("strange");
        let max_x = self.line.iter().map(|(_, x)| *x).max().expect("strange");
        let offset: usize = 0;
        debug_assert!(limit < self.distance_sum((min_y - offset, min_x - offset)));
        debug_assert!(limit < self.distance_sum((min_y - offset, max_x + offset)));
        debug_assert!(limit < self.distance_sum((max_y + offset, min_x - offset)));
        debug_assert!(limit < self.distance_sum((max_y + offset, max_x + offset)));
        let mut count = 0;
        for y in min_y..=max_y {
            for x in min_x..=max_x {
                if self.distance_sum((y, x)) < limit {
                    count += 1;
                }
            }
        }
        count
    }
}

impl Puzzle {
    fn shortest_to(&self, p: (usize, usize)) -> (usize, Vec<usize>) {
        use std::cmp::Ordering;
        let mut min_ids: Vec<usize> = Vec::new();
        let mut min_dist = usize::MAX;
        for (i, dest) in self.line.iter().enumerate() {
            let d = mdist!(p, dest);
            match d.cmp(&min_dist) {
                Ordering::Less => {
                    min_dist = d;
                    min_ids.clear();
                    min_ids.push(i);
                }
                Ordering::Equal => {
                    min_ids.push(i);
                }
                Ordering::Greater => (),
            }
        }
        (min_dist, min_ids)
    }
    fn distance_sum(&self, p: (usize, usize)) -> usize {
        self.line.iter().map(|q| mdist!(p, q)).sum::<usize>()
    }
}
