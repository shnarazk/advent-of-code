use crate::{
    framework::{aoc, AdventOfCode, ParseError},
    line_parser,
};

#[derive(Debug, Default, PartialEq)]
pub struct Puzzle {
    line: Vec<Vec<char>>,
}

fn floor(vec: &[char]) -> isize {
    match vec.get(0) {
        None => 0,
        Some('(') => 1 + floor(&vec[1..]),
        Some(')') => -1 + floor(&vec[1..]),
        _ => panic!(),
    }
}

fn to_basement(vec: &[char], level: isize) -> isize {
    match vec.get(0) {
        Some('(') => 1 + to_basement(&vec[1..], level + 1),
        Some(')') if level == 0 => 1,
        Some(')') => 1 + to_basement(&vec[1..], level - 1),
        _ => panic!(),
    }
}

#[aoc(2015, 1)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.line.push(line_parser::to_chars(block)?);
        Ok(())
    }
    fn after_insert(&mut self) {
        // dbg!(&self.line);
    }
    fn part1(&mut self) -> Self::Output1 {
        for l in self.line.iter() {
            dbg!(floor(l));
        }
        0
    }
    fn part2(&mut self) -> Self::Output2 {
        for l in self.line.iter() {
            dbg!(to_basement(l, 0));
        }
        0
    }
}
