//! <https://adventofcode.com/2023/day/2>
use {
    crate::framework::{aoc, AdventOfCode, ParseError},
    winnow::{
        ascii::{alpha1, digit1, space1},
        combinator::{delimited, separated, terminated},
        token::literal,
        PResult, Parser,
    },
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    index: usize,
    result1: usize,
    result2: usize,
}

#[aoc(2023, 2)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.index += 1;
        fn parse_color(block: &mut &str) -> PResult<(String, usize)> {
            let value = terminated(digit1, space1).parse_next(block)?;
            let color = alpha1(block)?;
            Ok((color.to_string(), value.parse::<usize>().unwrap()))
        }
        fn parse_block(block: &mut &str) -> PResult<(usize, usize, usize)> {
            let v: Vec<(String, usize)> =
                separated(1.., parse_color, literal(", ")).parse_next(block)?;
            let v3 = v.iter().fold((0, 0, 0), |acc, c_v| match c_v.0.as_str() {
                "red" => (c_v.1, acc.1, acc.2),
                "green" => (acc.0, c_v.1, acc.2),
                "blue" => (acc.0, acc.1, c_v.1),
                _ => panic!("can't"),
            });
            Ok(v3)
        }
        fn parse_line(block: &mut &str) -> PResult<Vec<(usize, usize, usize)>> {
            let _num = delimited(literal("Game "), digit1, literal(": ")).parse_next(block)?;
            let v = separated(1.., parse_block, literal("; ")).parse_next(block)?;
            Ok(v)
        }
        let s = block.to_string();
        let p = &mut s.as_str();
        let x = parse_line(p)?;
        let maxs = x.iter().fold((0, 0, 0), |acc, val| {
            (acc.0.max(val.0), acc.1.max(val.1), acc.2.max(val.2))
        });
        if maxs.0 <= 12 && maxs.1 <= 13 && maxs.2 <= 14 {
            self.result1 += self.index;
        }
        self.result2 += maxs.0 * maxs.1 * maxs.2;
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        self.result1
    }
    fn part2(&mut self) -> Self::Output2 {
        self.result2
    }
}
