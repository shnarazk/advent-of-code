//! <https://adventofcode.com/2023/day/8>
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        math, regex,
    },
    std::collections::HashMap,
};

#[derive(Debug, Default)]
pub struct Puzzle {
    head: Vec<char>,
    line: HashMap<String, (String, String)>,
}

#[aoc(2023, 8)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn header(&mut self, input: String) -> Result<String, ParseError> {
        let parser = regex!(r"^(.+)\n\n((.|\n)+)$");
        let segment = parser.captures(&input).ok_or(ParseError)?;
        self.head = segment[1].chars().collect::<Vec<_>>();
        Ok(segment[2].to_string())
    }
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        let b = block.bytes().collect::<Vec<_>>();
        let s1 = String::from_utf8(b[0..3].to_vec()).unwrap();
        let s2 = String::from_utf8(b[7..10].to_vec()).unwrap();
        let s3 = String::from_utf8(b[12..15].to_vec()).unwrap();
        self.line.insert(s1, (s2, s3));
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        self.traverse("AAA")
    }
    fn part2(&mut self) -> Self::Output2 {
        self.line
            .keys()
            .filter(|s| s.ends_with('A'))
            .map(|p| self.traverse(&p))
            .fold(1, math::lcm)
    }
}

impl Puzzle {
    fn traverse<'a>(&'a self, mut pos: &'a str) -> usize {
        for (i, s) in self.head.iter().cycle().enumerate() {
            if pos.ends_with('Z') {
                return i;
            }
            let (left, right) = self.line.get(pos).unwrap();
            pos = if *s == 'L' { left } else { right };
        }
        unreachable!()
    }
}
