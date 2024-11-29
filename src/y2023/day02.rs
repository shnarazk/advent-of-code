//! <https://adventofcode.com/2023/day/2>
use {
    crate::framework::{aoc, AdventOfCode, ParseError},
    nom::{
        bytes::complete::tag,
        character::complete::{alpha1, digit1, space1},
        multi::separated_list1,
        sequence::{delimited, terminated},
        IResult,
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
        fn parse_color(block: &str) -> IResult<&str, (String, usize)> {
            let (remain1, value) = terminated(digit1, space1)(block)?;
            let (remain2, color) = alpha1(remain1)?;
            Ok((
                remain2,
                (color.to_string(), value.parse::<usize>().unwrap()),
            ))
        }
        fn parse_block(block: &str) -> IResult<&str, (usize, usize, usize)> {
            let (i, v) = separated_list1(tag(", "), parse_color)(block)?;
            let v3 = v.iter().fold((0, 0, 0), |acc, c_v| match c_v.0.as_str() {
                "red" => (c_v.1, acc.1, acc.2),
                "green" => (acc.0, c_v.1, acc.2),
                "blue" => (acc.0, acc.1, c_v.1),
                _ => panic!("can't"),
            });
            Ok((i, v3))
        }
        fn parse_line(block: &str) -> IResult<&str, Vec<(usize, usize, usize)>> {
            let (remain1, _num) = delimited(tag("Game "), digit1, tag(": "))(block)?;
            let (remain2, v) = separated_list1(tag("; "), parse_block)(remain1)?;
            // dbg!(input);
            Ok((remain2, v))
        }
        let _ = dbg!(parse_line(block));
        let x = block
            .split(": ")
            .nth(1)
            .unwrap()
            .split(';')
            .map(|set| {
                let s = set
                    .split(", ")
                    .map(|b| {
                        let c = b.trim().split(' ').collect::<Vec<_>>();
                        match c[1] {
                            "red" => (c[0].to_owned().parse::<usize>().unwrap(), 0, 0),
                            "green" => (0, c[0].to_owned().parse::<usize>().unwrap(), 0),
                            "blue" => (0, 0, c[0].to_owned().parse::<usize>().unwrap()),
                            _ => panic!("cant"),
                        }
                    })
                    .collect::<Vec<_>>();
                s.iter().fold((0, 0, 0), |acc, val| {
                    (acc.0 + val.0, acc.1 + val.1, acc.2 + val.2)
                })
            })
            .collect::<Vec<_>>();
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
