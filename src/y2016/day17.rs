//! <https://adventofcode.com/2016/day/17>
use {
    crate::framework::{aoc_at, AdventOfCode, ParseError},
    md5::{Digest, Md5},
    std::{cmp::Reverse, collections::BinaryHeap},
};

type Dim2 = (usize, usize);

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: String,
}

#[aoc_at(2016, 17)]
impl AdventOfCode for Puzzle {
    type Output1 = String;
    type Output2 = usize;
    const DELIMITER: &'static str = "\n";
    fn parse_block(&mut self, _block: &str) -> Result<(), ParseError> {
        Ok(())
    }
    fn end_of_data(&mut self) {
        self.line = String::from("gdjjyniy");
    }
    fn part1(&mut self) -> Self::Output1 {
        let valid_range = 0..=3;
        let mut hasher = Hasher::new(&self.line);
        let mut to_visit: BinaryHeap<Reverse<(usize, Dim2, String)>> = BinaryHeap::new();
        to_visit.push(Reverse((0, (0, 0), String::from(""))));
        let dirs: [(isize, isize); 4] = [(-1, 0), (1, 0), (0, -1), (0, 1)];
        let goal: Dim2 = (3, 3);
        while let Some(Reverse((cost, pos, path))) = to_visit.pop() {
            if pos == goal {
                return path;
            }
            for (loc, dir) in dirs
                .iter()
                .map(|d| {
                    let y = pos.0 as isize + d.0;
                    let x = pos.1 as isize + d.1;
                    (valid_range.contains(&y) && valid_range.contains(&x))
                        .then_some((y as usize, x as usize))
                })
                .zip(hasher.get(&path).iter())
                .filter(|(p, b)| p.is_some() && b.is_some())
                .map(|(p, d)| (p.unwrap(), d.unwrap()))
            {
                let mut p = path.clone();
                p.push(dir);
                to_visit.push(Reverse((cost + 1, loc, p)))
            }
        }
        unreachable!()
    }
    fn part2(&mut self) -> Self::Output2 {
        let valid_range = 0..=3;
        let mut hasher = Hasher::new(&self.line);
        let mut to_visit: BinaryHeap<Reverse<(usize, Dim2, String)>> = BinaryHeap::new();
        to_visit.push(Reverse((0, (0, 0), String::from(""))));
        let dirs: [(isize, isize); 4] = [(-1, 0), (1, 0), (0, -1), (0, 1)];
        let goal: Dim2 = (3, 3);
        let mut longest = 0;
        while let Some(Reverse((cost, pos, path))) = to_visit.pop() {
            if pos == goal {
                longest = longest.max(path.len());
                continue;
            }
            for (loc, dir) in dirs
                .iter()
                .map(|d| {
                    let y = pos.0 as isize + d.0;
                    let x = pos.1 as isize + d.1;
                    (valid_range.contains(&y) && valid_range.contains(&x))
                        .then_some((y as usize, x as usize))
                })
                .zip(hasher.get(&path).iter())
                .filter(|(p, b)| p.is_some() && b.is_some())
                .map(|(p, d)| (p.unwrap(), d.unwrap()))
            {
                let mut p = path.clone();
                p.push(dir);
                to_visit.push(Reverse((cost + 1, loc, p)))
            }
        }
        longest
    }
}

struct Hasher<'a> {
    hasher: Md5,
    seed: &'a str,
}

impl<'a> Hasher<'a> {
    fn new(seed: &'a str) -> Self {
        Hasher {
            hasher: Md5::new(),
            seed,
        }
    }
    fn get(&mut self, path: &str) -> [Option<char>; 4] {
        let key = format!("{}{path}", self.seed);
        self.hasher.update(&key);
        let result = self.hasher.finalize_reset();
        let phrase = format!("{:x}", result)
            .chars()
            .take(4)
            .collect::<Vec<char>>();
        let is_open = |c: &char, d: char| ['b', 'c', 'd', 'e', 'f'].contains(c).then_some(d);
        [
            is_open(&phrase[0], 'U'),
            is_open(&phrase[1], 'D'),
            is_open(&phrase[2], 'L'),
            is_open(&phrase[3], 'R'),
        ]
    }
}
