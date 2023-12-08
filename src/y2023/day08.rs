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
        let mut i = 0;
        let mut cnt = 0;
        let mut pos = "AAA";
        while pos != "ZZZ" {
            let Some((left, right)) = self.line.get(pos) else {
                unreachable!();
            };
            pos = if self.head[i] == 'L' { left } else { right };
            i += 1;
            cnt += 1;
            if i == self.head.len() {
                i = 0;
            }
        }
        cnt
    }
    fn part2(&mut self) -> Self::Output2 {
        let pos = self
            .line
            .keys()
            .filter(|s| s.ends_with('A'))
            .cloned()
            .collect::<Vec<_>>();
        let mut ans: usize = 1;
        for p in pos.iter() {
            let mut pos = p;
            let mut i = 0;
            let mut cnt = 0;
            while !pos.ends_with('Z') {
                let (left, right) = self.line.get(pos).unwrap();
                pos = if self.head[i] == 'L' { left } else { right };
                i += 1;
                cnt += 1;
                if i == self.head.len() {
                    i = 0;
                }
            }
            ans = math::lcm(ans, cnt);
        }
        ans
    }
}
