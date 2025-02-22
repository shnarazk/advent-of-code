//! <https://adventofcode.com/2022/day/14>
use {
    crate::framework::{AdventOfCode, ParseError, aoc},
    std::collections::HashSet,
};

type Loc = (usize, usize);

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Puzzle {
    line: Vec<Vec<Loc>>,
    map: HashSet<Loc>,
    threshold: usize,
}

#[aoc(2022, 14)]
impl AdventOfCode for Puzzle {
    fn prepare(&mut self, input: &str) -> Result<(), ParseError> {
        self.line = input
            .lines()
            .map(|line| {
                line.split(" -> ")
                    .map(|chunk| {
                        let v = chunk
                            .split(',')
                            .map(|d| d.parse::<usize>().unwrap())
                            .collect::<Vec<usize>>();
                        (v[0], v[1])
                    })
                    .collect::<Vec<Loc>>()
            })
            .collect();
        for line in self.line.iter() {
            for start_end in line.windows(2) {
                let dx: isize = (start_end[1].0 as isize - start_end[0].0 as isize).signum();
                let dy: isize = (start_end[1].1 as isize - start_end[0].1 as isize).signum();
                let mut pos = start_end[0];
                while pos != start_end[1] {
                    if self.threshold < pos.1 {
                        self.threshold = pos.1;
                    }
                    self.map.insert(pos);
                    pos.0 = (pos.0 as isize + dx) as usize;
                    pos.1 = (pos.1 as isize + dy) as usize;
                }
                self.map.insert(start_end[1]);
            }
        }
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        let num_wall = self.map.len();
        'next_sand: loop {
            let mut pos: Loc = (500, 0);
            let mut tmp = pos;
            'moving: loop {
                if self.threshold < pos.1 {
                    break 'next_sand;
                }
                tmp.1 += 1;
                if !self.map.contains(&tmp) {
                    pos = tmp;
                    continue 'moving;
                }
                tmp.0 -= 1;
                if !self.map.contains(&tmp) {
                    pos = tmp;
                    continue 'moving;
                }
                tmp.0 += 2;
                if !self.map.contains(&tmp) {
                    pos = tmp;
                    continue 'moving;
                }
                self.map.insert(pos);
                continue 'next_sand;
            }
        }
        self.map.len() - num_wall
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut num_sands = 0;
        let mut rows: HashSet<usize> = HashSet::new();
        let mut next: HashSet<usize> = HashSet::new();
        rows.insert(500);
        for depth in 0..=self.threshold + 1 {
            for x in rows.iter() {
                for xx in x - 1..=x + 1 {
                    if !self.map.contains(&(xx, depth + 1)) {
                        next.insert(xx);
                    }
                }
            }
            num_sands += rows.len();
            rows.clear();
            std::mem::swap(&mut rows, &mut next);
        }
        num_sands
    }
}
