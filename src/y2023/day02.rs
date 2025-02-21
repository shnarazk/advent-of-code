//! <https://adventofcode.com/2023/day/2>
use {
    crate::framework::{AdventOfCode, ParseError, aoc},
    winnow::{
        ModalResult, Parser,
        ascii::{alpha1, digit1, space1},
        combinator::{delimited, separated, terminated},
    },
};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    index: usize,
    result1: usize,
    result2: usize,
}

#[aoc(2023, 2)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, input: &str) -> Result<(), ParseError> {
        for mut l in input.lines() {
            self.index += 1;
            fn parse_color(block: &mut &str) -> ModalResult<(String, usize)> {
                let value = terminated(digit1, space1).parse_next(block)?;
                let color = alpha1(block)?;
                Ok((color.to_string(), value.parse::<usize>().unwrap()))
            }
            fn parse_block(block: &mut &str) -> ModalResult<(usize, usize, usize)> {
                let v: Vec<(String, usize)> =
                    separated(1.., parse_color, ", ").parse_next(block)?;
                let v3 = v.iter().fold((0, 0, 0), |acc, c_v| match c_v.0.as_str() {
                    "red" => (c_v.1, acc.1, acc.2),
                    "green" => (acc.0, c_v.1, acc.2),
                    "blue" => (acc.0, acc.1, c_v.1),
                    _ => panic!("can't"),
                });
                Ok(v3)
            }
            fn parse_line(block: &mut &str) -> ModalResult<Vec<(usize, usize, usize)>> {
                let _num = delimited("Game ", digit1, ": ").parse_next(block)?;
                let v = separated(1.., parse_block, "; ").parse_next(block)?;
                Ok(v)
            }
            let x = parse_line(&mut l)?;
            let maxs = x.iter().fold((0, 0, 0), |acc, val| {
                (acc.0.max(val.0), acc.1.max(val.1), acc.2.max(val.2))
            });
            if maxs.0 <= 12 && maxs.1 <= 13 && maxs.2 <= 14 {
                self.result1 += self.index;
            }
            self.result2 += maxs.0 * maxs.1 * maxs.2;
        }
        Self::parsed()
    }
    fn part1(&mut self) -> Self::Output1 {
        self.result1
    }
    fn part2(&mut self) -> Self::Output2 {
        self.result2
    }
}
