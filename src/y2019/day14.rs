//! <https://adventofcode.com/2019/day/14>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::neighbors,
        line_parser, regex,
    },
    std::collections::HashMap,
};

type ChemicalUnit = (String, usize);

#[derive(Debug, Default, Eq, PartialEq)]
pub struct Puzzle {
    line: Vec<(Vec<ChemicalUnit>, ChemicalUnit)>,
}

fn parse_chemical_unit(s: &str) -> Result<ChemicalUnit, ParseError> {
    let parser = regex!(r"^(\d+) ([A-Z]+)");
    let segment = parser.captures(s).ok_or(ParseError)?;
    Ok((segment[2].to_string(), segment[1].parse::<usize>()?))
}

#[aoc(2019, 14)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        let parser = regex!(r"^((\d+ [A-Z]+, )*)(\d+ [A-Z]+) => (\d+ [A-Z]+)");
        let segment = parser.captures(block).ok_or(ParseError)?;
        let mut vec = segment[1]
            .split(", ")
            .filter(|seg| !seg.is_empty())
            .map(|seg| parse_chemical_unit(seg).unwrap())
            .collect::<Vec<ChemicalUnit>>();
        vec.push(parse_chemical_unit(&segment[3])?);
        self.line.push((vec, parse_chemical_unit(&segment[4])?));
        Ok(())
    }
    fn after_insert(&mut self) {
        // dbg!(&self.line);
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut hash: HashMap<&str, (&[ChemicalUnit], usize)> = HashMap::new();
        for (vec, (c, u)) in self.line.iter() {
            hash.insert(c, (vec, *u));
        }
        dbg!(&hash);
        0
    }
    fn part2(&mut self) -> Self::Output2 {
        0
    }
}

#[cfg(feature = "y2019")]
#[cfg(test)]
mod test {
    use {
        super::*,
        crate::framework::{Answer, Description},
    };

    // #[test]
    // fn test_part1() {
    //     assert_eq!(
    //         Puzzle::solve(Description::TestData("".to_string()), 1),
    //         Answer::Part1(0)
    //     );
    // }
}
