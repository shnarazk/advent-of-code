//! <https://adventofcode.com/2023/day/8>
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        math,
    },
    std::collections::HashMap,
    winnow::{
        ascii::{alphanumeric1, newline},
        combinator::{separated, terminated},
        token::literal,
        PResult, Parser,
    },
};

#[derive(Debug, Default)]
pub struct Puzzle {
    head: Vec<char>,
    line: HashMap<String, (String, String)>,
}

fn parse_header(input: &mut &str) -> PResult<String> {
    let label = terminated(alphanumeric1, literal("\n\n")).parse_next(input)?;
    Ok(label.to_string())
}

// fn parse(str: &str) -> IResult<&str, Data>;
fn parse_block(input: &mut &str) -> PResult<(String, (String, String))> {
    let label = terminated(alphanumeric1, literal(" = (")).parse_next(input)?;
    let child1 = terminated(alphanumeric1, literal(", ")).parse_next(input)?;
    let child2 = terminated(alphanumeric1, literal(")")).parse_next(input)?;
    Ok((label.to_string(), (child1.to_string(), child2.to_string())))
}

#[aoc(2023, 8)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn parse(&mut self, input: String) -> Result<String, ParseError> {
        let str = &mut input.as_str();
        let label = parse_header(str)?;
        self.head = label.chars().collect::<Vec<_>>();
        let v: Vec<(String, (String, String))> =
            separated(1.., parse_block, newline).parse_next(str)?;
        self.line = v
            .iter()
            .cloned()
            .collect::<HashMap<String, (String, String)>>();
        Ok("".to_string())
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
