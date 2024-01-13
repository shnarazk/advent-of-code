//! <https://adventofcode.com/2018/day/25>
use {
    crate::{
        framework::{aoc_at, AdventOfCode, ParseError},
        line_parser,
    },
    std::collections::HashMap,
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Vec<isize>>,
}

#[aoc_at(2018, 25)]
impl AdventOfCode for Puzzle {
    type Output1 = usize;
    type Output2 = String;
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.line.push(line_parser::to_isizes(block, ',')?);
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut constellation: HashMap<usize, usize> = HashMap::new();
        let mut constellation_id = 1;
        constellation.insert(0, constellation_id);
        'next_point: for (i, p) in self.line.iter().enumerate().skip(1) {
            for (j, q) in self.line.iter().enumerate().take(i - 1) {
                let dist: usize = (p[0] - q[0]).unsigned_abs()
                    + (p[1] - q[1]).unsigned_abs()
                    + (p[2] - q[2]).unsigned_abs()
                    + (p[3] - q[3]).unsigned_abs();
                if dist <= 3 {
                    let cid = constellation[&j];
                    constellation.insert(i, cid);
                    continue 'next_point;
                }
            }
            constellation_id += 1;
            constellation.insert(i, constellation_id);
        }
        // dbg!(constellation_id);
        for (i, p) in self.line.iter().enumerate() {
            for (j, q) in self.line.iter().enumerate().skip(i) {
                let ci = constellation[&i];
                let cj = constellation[&j];
                if ci == cj {
                    continue;
                }
                let dist: usize = (p[0] - q[0]).unsigned_abs()
                    + (p[1] - q[1]).unsigned_abs()
                    + (p[2] - q[2]).unsigned_abs()
                    + (p[3] - q[3]).unsigned_abs();
                if dist <= 3 {
                    // renumber cj to ci
                    for (_, v) in constellation.iter_mut() {
                        if *v == cj {
                            *v = ci;
                        }
                    }
                    constellation_id -= 1;
                }
            }
        }
        // dbg!(constellation.values().collect::<HashSet<_>>().len());
        constellation_id
    }
    fn part2(&mut self) -> Self::Output2 {
        "Happy Holidays!".to_string()
    }
}
