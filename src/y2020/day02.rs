//! <https://adventofcode.com/2020/day/2>
use {
    crate::framework::{aoc, AdventOfCode, ParseError},
    lazy_static::lazy_static,
    regex::Regex,
};

#[derive(Debug, Default, PartialEq)]
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
    lazy_static! {
        static ref PARSER: Regex =
            Regex::new(r"^([0-9]+)-([0-9]+) ([a-zA-Z]): (.*)$").expect("wrong regex");
    }
    if let Some(m) = PARSER.captures(str) {
        let mi = m[1].parse::<usize>().unwrap();
        let ma = m[2].parse::<usize>().unwrap();
        let target: char = m[3].chars().next().unwrap();
        println!("min:{}, max:{}, letter:{}, body: {}", mi, ma, target, &m[4]);
        let occ = m[4].chars().filter(|c| *c == target).count();
        (mi <= occ && occ <= ma) as usize
    } else {
        0
    }
}

fn check_line2(str: &str) -> usize {
    lazy_static! {
        static ref PARSER: Regex =
            Regex::new(r"^([0-9]+)-([0-9]+) ([a-zA-Z]): (.*)$").expect("wrong regex");
    }
    if let Some(m) = PARSER.captures(str) {
        let pos1 = m[1].parse::<usize>().unwrap();
        let pos2 = m[2].parse::<usize>().unwrap();
        let ch: char = m[3].chars().next().unwrap();
        let target: &str = &m[4];
        let p1 = target.chars().nth(pos1 - 1) == Some(ch);
        let p2 = target.chars().nth(pos2 - 1) == Some(ch);
        if p1 ^ p2 {
            println!(
                "OK: p1:{}=>{}, p2:{}=>{}, letter:{}, body: {}",
                pos1,
                target.chars().nth(pos1 - 1).unwrap(),
                pos2,
                target.chars().nth(pos2 - 1).unwrap(),
                ch,
                target
            );
        } else {
            println!(
                "NG: p1:{}=>{}, p2:{}=>{}, letter:{}, body: {}",
                pos1,
                target.chars().nth(pos1 - 1).unwrap(),
                pos2,
                target.chars().nth(pos2 - 1).unwrap(),
                ch,
                target
            );
        }
        (p1 ^ p2) as usize
    } else {
        0
    }
}

#[cfg(feature = "y2020")]
#[cfg(test)]
mod test {
    use {
        super::*,
        crate::framework::{Answer, Description},
    };

    const TEST: &str = "\
1-3 a: abcde
1-3 b: cdefg
2-9 c: ccccccccc";

    #[test]
    fn test1() {
        assert_eq!(
            Puzzle::solve(Description::TestData(TEST.to_string()), 1),
            Answer::Part1(2)
        );
    }

    #[test]
    fn test2() {
        assert_eq!(
            Puzzle::solve(Description::TestData(TEST.to_string()), 2),
            Answer::Part2(1)
        );
    }
}
