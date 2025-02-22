//! <https://adventofcode.com/2015/day/16>
use crate::framework::{AdventOfCode, ParseError, aoc};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Sue {
    id: usize,
    children: Option<usize>,
    cats: Option<usize>,
    samoyeds: Option<usize>,
    pomeranians: Option<usize>,
    akitas: Option<usize>,
    vizslas: Option<usize>,
    goldfish: Option<usize>,
    trees: Option<usize>,
    cars: Option<usize>,
    perfumes: Option<usize>,
}

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Sue>,
}

mod parser {
    use {
        super::*,
        crate::parser::parse_usize,
        winnow::{
            ModalResult, Parser,
            ascii::{alpha1, newline},
            combinator::{separated, seq},
        },
    };

    fn parse_sue(s: &mut &str) -> ModalResult<Sue> {
        seq!(
            _: "Sue ", parse_usize, _: ": ",
            separated(1.., seq!(alpha1, _: ": ", parse_usize), ", ")
        )
        .map(|(n, v): (usize, Vec<(&str, usize)>)| {
            let mut sue = Sue {
                id: n,
                ..Sue::default()
            };
            for (prop, val) in v {
                match prop {
                    "children" => sue.children = Some(val),
                    "cats" => sue.cats = Some(val),
                    "samoyeds" => sue.samoyeds = Some(val),
                    "pomeranians" => sue.pomeranians = Some(val),
                    "akitas" => sue.akitas = Some(val),
                    "vizslas" => sue.vizslas = Some(val),
                    "goldfish" => sue.goldfish = Some(val),
                    "trees" => sue.trees = Some(val),
                    "cars" => sue.cars = Some(val),
                    "perfumes" => sue.perfumes = Some(val),
                    _ => panic!(),
                }
            }
            sue
        })
        .parse_next(s)
    }

    pub fn parse(s: &mut &str) -> ModalResult<Vec<Sue>> {
        separated(1.., parse_sue, newline).parse_next(s)
    }
}

#[aoc(2015, 16)]
impl AdventOfCode for Puzzle {
    fn prepare(&mut self, mut input: &str) -> Result<(), ParseError> {
        self.line = parser::parse(&mut input)?;
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        self.line
            .iter()
            .filter(|sue| {
                sue.children.is_none_or(|v| v == 3)
                    && sue.cats.is_none_or(|v| v == 7)
                    && sue.samoyeds.is_none_or(|v| v == 2)
                    && sue.pomeranians.is_none_or(|v| v == 3)
                    && sue.akitas.is_none_or(|v| v == 0)
                    && sue.vizslas.is_none_or(|v| v == 0)
                    && sue.goldfish.is_none_or(|v| v == 5)
                    && sue.trees.is_none_or(|v| v == 3)
                    && sue.cars.is_none_or(|v| v == 2)
                    && sue.perfumes.is_none_or(|v| v == 1)
            })
            .map(|sue| sue.id)
            .max()
            .unwrap()
    }
    fn part2(&mut self) -> Self::Output2 {
        let they = self
            .line
            .iter()
            .filter(|sue| {
                sue.children.is_none_or(|v| v == 3)
                    && sue.cats.is_none_or(|v| v > 7)
                    && sue.samoyeds.is_none_or(|v| v == 2)
                    && sue.pomeranians.is_none_or(|v| v < 3)
                    && sue.akitas.is_none_or(|v| v == 0)
                    && sue.vizslas.is_none_or(|v| v == 0)
                    && sue.goldfish.is_none_or(|v| v < 5)
                    && sue.trees.is_none_or(|v| v > 3)
                    && sue.cars.is_none_or(|v| v == 2)
                    && sue.perfumes.is_none_or(|v| v == 1)
            })
            .collect::<Vec<_>>();
        // dbg!(&they);
        they[0].id
    }
}
