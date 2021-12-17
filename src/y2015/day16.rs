//! <https://adventofcode.com/2015/day/>
use {
    crate::framework::{aoc, AdventOfCode, ParseError},
    lazy_static::lazy_static,
    regex::Regex,
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
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

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Sue>,
}

#[aoc(2015, 16)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        lazy_static! {
            static ref PARSER: Regex =
                Regex::new(r"^Sue ([0-9]+): (([a-z]+: [0-9]+, )*[a-z]+: [0-9]+)$").expect("wrong");
        }
        let segment = PARSER.captures(block).ok_or(ParseError)?;
        // print!("{:>4} - ", segment[1].parse::<usize>()?);
        let mut sue: Sue = Sue {
            id: segment[1].parse::<usize>()?,
            ..Sue::default()
        };
        for seg in segment[2].split(',') {
            let mut tokens = seg.split(':');
            let prop = tokens.next().ok_or(ParseError)?.trim();
            let val = tokens.next().ok_or(ParseError)?.trim().parse::<usize>()?;
            // print!("{:>12}: {:>3} ", prop, val);
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
        // println!();
        self.line.push(sue);
        Ok(())
    }
    fn after_insert(&mut self) {
        dbg!(&self.line);
        // assert_eq!(self.line.len(), 500);
    }
    fn part1(&mut self) -> Self::Output1 {
        self.line
            .iter()
            .filter(|sue| {
                sue.children.map_or(true, |v| v == 3)
                    && sue.cats.map_or(true, |v| v == 7)
                    && sue.samoyeds.map_or(true, |v| v == 2)
                    && sue.pomeranians.map_or(true, |v| v == 3)
                    && sue.akitas.map_or(true, |v| v == 0)
                    && sue.vizslas.map_or(true, |v| v == 0)
                    && sue.goldfish.map_or(true, |v| v == 5)
                    && sue.trees.map_or(true, |v| v == 3)
                    && sue.cars.map_or(true, |v| v == 2)
                    && sue.perfumes.map_or(true, |v| v == 1)
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
                sue.children.map_or(true, |v| v == 3)
                    && sue.cats.map_or(true, |v| v > 7)
                    && sue.samoyeds.map_or(true, |v| v == 2)
                    && sue.pomeranians.map_or(true, |v| v < 3)
                    && sue.akitas.map_or(true, |v| v == 0)
                    && sue.vizslas.map_or(true, |v| v == 0)
                    && sue.goldfish.map_or(true, |v| v < 5)
                    && sue.trees.map_or(true, |v| v > 3)
                    && sue.cars.map_or(true, |v| v == 2)
                    && sue.perfumes.map_or(true, |v| v == 1)
            })
            .collect::<Vec<_>>();
        dbg!(&they);
        they[0].id
    }
}
