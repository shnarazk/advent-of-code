//! <https://adventofcode.com/2023/day/8>
use {
    crate::{
        framework::{AdventOfCode, ParseError, aoc},
        math,
    },
    std::collections::HashMap,
    winnow::{
        ModalResult, Parser,
        ascii::{alphanumeric1, newline},
        combinator::{separated, terminated},
    },
};

#[derive(Clone, Debug, Default)]
pub struct Puzzle {
    head: Vec<char>,
    line: HashMap<String, (String, String)>,
}

fn parse_header(input: &mut &str) -> ModalResult<String> {
    let label = terminated(alphanumeric1, "\n\n").parse_next(input)?;
    Ok(label.to_string())
}

// fn parse(str: &str) -> IResult<&str, Data>;
fn parse_block(input: &mut &str) -> ModalResult<(String, (String, String))> {
    let label = terminated(alphanumeric1, " = (").parse_next(input)?;
    let child1 = terminated(alphanumeric1, ", ").parse_next(input)?;
    let child2 = terminated(alphanumeric1, ")").parse_next(input)?;
    Ok((label.to_string(), (child1.to_string(), child2.to_string())))
}

#[aoc(2023, 8)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, mut input: &str) -> Result<(), ParseError> {
        let label = parse_header(&mut input)?;
        self.head = label.chars().collect::<Vec<_>>();
        let v: Vec<(String, (String, String))> =
            separated(1.., parse_block, newline).parse_next(&mut input)?;
        self.line = v
            .iter()
            .cloned()
            .collect::<HashMap<String, (String, String)>>();
        Self::parsed()
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
