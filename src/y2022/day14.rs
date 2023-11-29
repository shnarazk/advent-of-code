//! <https://adventofcode.com/2022/day/14>
use {
    crate::framework::{aoc, AdventOfCode, ParseError},
    std::collections::HashSet,
};

type Loc = (usize, usize);
trait Below {
    fn below(&self) -> Self;
}
impl Below for Loc {
    fn below(&self) -> Self {
        (self.0, self.1 + 1)
    }
}

#[derive(Debug, Default, Eq, PartialEq)]
pub struct Puzzle {
    line: Vec<Vec<Loc>>,
    map: HashSet<Loc>,
    threshold: usize,
}

#[aoc(2022, 14)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.line.push(
            block
                .split(" -> ")
                .map(|chunk| {
                    let v = chunk
                        .split(',')
                        .map(|d| d.parse::<usize>().expect("!"))
                        .collect::<Vec<usize>>();
                    (v[0], v[1])
                })
                .collect::<Vec<Loc>>(),
        );
        Ok(())
    }
    fn wrap_up(&mut self) {
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
        dbg!(&self.line.len());
        dbg!(&self.map.len());
        dbg!(self.threshold);
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
        let num_wall = self.map.len();
        'next_sand: loop {
            let mut pos: Loc = (500, 0);
            let mut tmp = pos;
            'moving: loop {
                tmp.1 += 1;
                if !self.map.contains(&tmp) && tmp.1 <= self.threshold + 1 {
                    pos = tmp;
                    continue 'moving;
                }
                tmp.0 -= 1;
                if !self.map.contains(&tmp) && tmp.1 <= self.threshold + 1 {
                    pos = tmp;
                    continue 'moving;
                }
                tmp.0 += 2;
                if !self.map.contains(&tmp) && tmp.1 <= self.threshold + 1 {
                    pos = tmp;
                    continue 'moving;
                }
                self.map.insert(pos);
                if pos == (500, 0) {
                    break 'next_sand;
                }
                continue 'next_sand;
            }
        }
        self.map.len() - num_wall
    }
}
