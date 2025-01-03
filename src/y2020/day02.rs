//! <https://adventofcode.com/2020/day/2>
use crate::{
    framework::{aoc, AdventOfCode, ParseError},
    regex,
};

#[derive(Clone, Debug, Default, PartialEq)]
pub struct Puzzle {
    line: Vec<String>,
}

#[aoc(2020, 2)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.line.push(block.to_string());
        Ok(())
    }
    fn part1(&mut self) -> usize {
        self.line.iter().map(|s| check_line1(s)).sum::<usize>()
    }
    fn part2(&mut self) -> usize {
        self.line.iter().map(|s| check_line2(s)).sum::<usize>()
    }
}

fn check_line1(str: &str) -> usize {
    let parser = regex!(r"^([0-9]+)-([0-9]+) ([a-zA-Z]): (.*)$");
    if let Some(m) = parser.captures(str) {
        let mi = m[1].parse::<usize>().unwrap();
        let ma = m[2].parse::<usize>().unwrap();
        let target: char = m[3].chars().next().unwrap();
        // println!("min:{}, max:{}, letter:{}, body: {}", mi, ma, target, &m[4]);
        let occ = m[4].chars().filter(|c| *c == target).count();
        (mi <= occ && occ <= ma) as usize
    } else {
        0
    }
}

fn check_line2(str: &str) -> usize {
    let parser = regex!(r"^([0-9]+)-([0-9]+) ([a-zA-Z]): (.*)$");
    if let Some(m) = parser.captures(str) {
        let pos1 = m[1].parse::<usize>().unwrap();
        let pos2 = m[2].parse::<usize>().unwrap();
        let ch: char = m[3].chars().next().unwrap();
        let target: &str = &m[4];
        let p1 = target.chars().nth(pos1 - 1) == Some(ch);
        let p2 = target.chars().nth(pos2 - 1) == Some(ch);
        // if p1 ^ p2 {
        //     println!(
        //         "OK: p1:{}=>{}, p2:{}=>{}, letter:{}, body: {}",
        //         pos1,
        //         target.chars().nth(pos1 - 1).unwrap(),
        //         pos2,
        //         target.chars().nth(pos2 - 1).unwrap(),
        //         ch,
        //         target
        //     );
        // } else {
        //     println!(
        //         "NG: p1:{}=>{}, p2:{}=>{}, letter:{}, body: {}",
        //         pos1,
        //         target.chars().nth(pos1 - 1).unwrap(),
        //         pos2,
        //         target.chars().nth(pos2 - 1).unwrap(),
        //         ch,
        //         target
        //     );
        // }
        (p1 ^ p2) as usize
    } else {
        0
    }
}
