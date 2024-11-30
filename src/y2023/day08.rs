//! <https://adventofcode.com/2023/day/8>
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        math,
    },
    nom::{
        bytes::complete::tag,
        character::complete::{alphanumeric1, newline},
        multi::separated_list1,
        sequence::terminated,
        IResult,
    },
    std::collections::HashMap,
};

#[derive(Debug, Default)]
pub struct Puzzle {
    head: Vec<char>,
    line: HashMap<String, (String, String)>,
}

fn parse_header(input: &str) -> IResult<&str, String> {
    let (remain1, label) = terminated(alphanumeric1, tag("\n\n"))(input)?;
    Ok((remain1, label.to_string()))
}

// fn parse(str: &str) -> IResult<&str, Data>;
fn parse_block(input: &str) -> IResult<&str, (String, (String, String))> {
    let (remain1, label) = terminated(alphanumeric1, tag(" = ("))(input)?;
    let (remain2, child1) = terminated(alphanumeric1, tag(", "))(remain1)?;
    let (remain3, child2) = terminated(alphanumeric1, tag(")"))(remain2)?;
    Ok((
        remain3,
        (label.to_string(), (child1.to_string(), child2.to_string())),
    ))
}

#[aoc(2023, 8)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn header(&mut self, input: String) -> Result<String, ParseError> {
        let str = input.as_str();
        let Ok((remain1, label)) = parse_header(str) else {
            return Err(ParseError);
        };
        self.head = label.chars().collect::<Vec<_>>();
        let Ok((remain2, v)) = separated_list1(newline, parse_block)(remain1) else {
            return Err(ParseError);
        };
        self.line = v
            .iter()
            .cloned()
            .collect::<HashMap<String, (String, String)>>();
        Ok(remain2.to_string())
    }
    fn insert(&mut self, _block: &str) -> Result<(), ParseError> {
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        self.traverse("AAA")
    }
    fn part2(&mut self) -> Self::Output2 {
        self.line
            .keys()
            .filter(|s| s.ends_with('A'))
            .map(|p| self.traverse(p))
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
