//! <https://adventofcode.com/2020/day/17>

use crate::framework::ConfigAoC;
use {
    crate::framework::{aoc, AdventOfCode, Answer, Description, ParseError},
    std::{cmp::PartialEq, collections::HashMap, fmt::Debug, hash::Hash},
};

#[derive(Debug, Default)]
pub struct Puzzle {}

#[aoc(2020, 17)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "";
    fn insert(&mut self, _block: &str) -> Result<(), ParseError> {
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        0
    }
    fn part2(&mut self) -> Self::Output2 {
        0
    }
    fn solve(config: ConfigAoC) -> Answer<Self::Output1, Self::Output2> {
        match config.part {
            1 => World::<LOC>::solve(config),
            2 => World::<LOC4>::solve(config),
            _ => {
                let c1 = ConfigAoC {
                    part: 1,
                    ..ConfigAoC::default()
                };
                let c2 = ConfigAoC {
                    part: 2,
                    ..ConfigAoC::default()
                };
                match (World::<LOC>::solve(c1), World::<LOC4>::solve(c2)) {
                    (Answer::Part1(a), Answer::Part2(b)) => Answer::Answers(a, b),
                    _ => unreachable!(),
                }
            }
        }
    }
}

const RANGE: isize = 17;

#[allow(clippy::upper_case_acronyms)]
type LOC = (isize, isize, isize);

#[allow(clippy::upper_case_acronyms)]
type LOC4 = (isize, isize, isize, isize);

#[derive(Debug, Default, PartialEq)]
struct World<DIM: Eq + Default + Hash + PartialEq> {
    loc: HashMap<DIM, bool>,
    generation: usize,
}

#[derive(Debug, Default, PartialEq)]
struct World0 {
    loc: HashMap<LOC, bool>,
    generation: usize,
}

#[derive(Debug, Default, PartialEq)]
struct World4 {
    loc: HashMap<LOC4, bool>,
    generation: usize,
}

trait CellParser {
    type Element;
    fn default_() -> Self;
    fn parse_(self, block: &str) -> Self;
    fn neighbors(&mut self, l: Self::Element) -> (usize, usize);
    fn next(&mut self) -> Self;
    fn actives(&self) -> usize;
}

impl CellParser for World<LOC> {
    type Element = LOC;
    fn default_() -> Self {
        Self {
            loc: HashMap::new(),
            generation: 0,
        }
    }
    fn parse_(mut self, block: &str) -> Self {
        let mut vec: Vec<LOC> = Vec::new();
        let z = 0;
        let offset = (block.split('\n').count() as isize - 1) / 2;
        let mut i = -offset;
        let mut j = -offset;
        for l in block.split('\n') {
            for c in l.chars() {
                if c == '#' {
                    vec.push((z, i, j));
                }
                j += 1;
            }
            j = -offset;
            i += 1;
        }
        for l in vec {
            *self.loc.entry(l).or_insert(false) = true;
        }
        self
    }
    fn neighbors(&mut self, l: LOC) -> (usize, usize) {
        let mut actives = 0;
        let mut inactives = 0;
        for z in -1..=1 {
            for i in -1..=1 {
                for j in -1..=1 {
                    if z == 0 && i == 0 && j == 0 {
                        continue;
                    }
                    if *self.get_entry((l.0 + z, l.1 + i, l.2 + j)) {
                        actives += 1;
                    } else {
                        inactives += 1;
                    }
                }
            }
        }
        (inactives, actives)
    }
    fn next(&mut self) -> Self {
        let mut next = Self::default_();
        for z in -RANGE..=RANGE {
            for i in -RANGE..=RANGE {
                for j in -RANGE..=RANGE {
                    let l = (z, i, j);
                    let na = self.neighbors(l).1;
                    let new_entry = next.get_entry(l);
                    if *self.get_entry(l) {
                        *new_entry = na == 2 || na == 3;
                    } else {
                        *new_entry = na == 3;
                    }
                }
            }
        }
        next.generation = self.generation + 1;
        next
    }
    fn actives(&self) -> usize {
        let mut count = 0;
        for z in -RANGE..=RANGE {
            for i in -RANGE..=RANGE {
                for j in -RANGE..=RANGE {
                    if let Some(true) = self.loc.get(&(z, i, j)) {
                        count += 1;
                    }
                }
            }
        }
        count
    }
}

impl CellParser for World<LOC4> {
    type Element = LOC4;
    fn default_() -> Self {
        Self {
            loc: HashMap::new(),
            generation: 0,
        }
    }
    fn parse_(mut self, block: &str) -> Self {
        let mut vec: Vec<LOC4> = Vec::new();
        let t = 0;
        let z = 0;
        let offset = (block.split('\n').count() as isize - 1) / 2;
        let mut i = -offset;
        let mut j = -offset;
        for l in block.split('\n') {
            for c in l.chars() {
                if c == '#' {
                    vec.push((t, z, i, j));
                }
                j += 1;
            }
            j = -offset;
            i += 1;
        }
        for l in vec {
            *self.loc.entry(l).or_insert(false) = true;
        }
        self
    }
    fn neighbors(&mut self, l: LOC4) -> (usize, usize) {
        let mut actives = 0;
        let mut inactives = 0;
        for t in -1..=1 {
            for z in -1..=1 {
                for i in -1..=1 {
                    for j in -1..=1 {
                        if t == 0 && z == 0 && i == 0 && j == 0 {
                            continue;
                        }
                        if *self.get_entry((l.0 + t, l.1 + z, l.2 + i, l.3 + j)) {
                            actives += 1;
                        } else {
                            inactives += 1;
                        }
                    }
                }
            }
        }
        (inactives, actives)
    }
    fn next(&mut self) -> Self {
        let mut next = Self::default_();
        for t in -RANGE..=RANGE {
            for z in -RANGE..=RANGE {
                for i in -RANGE..=RANGE {
                    for j in -RANGE..=RANGE {
                        let l = (t, z, i, j);
                        let na = self.neighbors(l).1;
                        let new_entry = next.get_entry(l);
                        if *self.get_entry(l) {
                            *new_entry = na == 2 || na == 3;
                        } else {
                            *new_entry = na == 3;
                        }
                    }
                }
            }
        }
        next.generation = self.generation + 1;
        next
    }
    fn actives(&self) -> usize {
        let mut count = 0;
        for t in -RANGE..=RANGE {
            for z in -RANGE..=RANGE {
                for i in -RANGE..=RANGE {
                    for j in -RANGE..=RANGE {
                        if let Some(true) = self.loc.get(&(t, z, i, j)) {
                            count += 1;
                        }
                    }
                }
            }
        }
        count
    }
}

#[aoc(2020, 17)]
impl<DIM: Debug + Default + Eq + Hash + PartialEq> AdventOfCode for World<DIM>
where
    World<DIM>: CellParser,
{
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, _block: &str) -> Result<(), ParseError> {
        Ok(())
    }
    fn parse(config: ConfigAoC) -> Result<Self, ParseError> {
        let description = match config.alt {
            Some(ext) if ext == "-" => Description::TestData("".to_string()),
            Some(ext) => Description::FileTag(ext.to_string()),
            None => Description::None,
        };
        Ok(Self::default().parse_(&Self::load(description)?))
        // Ok(Self::default().parse_(&Self::load(desc)?))
    }
    fn part1(&mut self) -> usize {
        self.next().next().next().next().next().next().actives()
    }
    fn part2(&mut self) -> usize {
        self.next().next().next().next().next().next().actives()
    }
}

impl<DIM: Default + Eq + Hash + PartialEq> World<DIM>
where
    World<DIM>: CellParser,
{
    fn get_entry(&mut self, l: DIM) -> &mut bool {
        self.loc.entry(l).or_insert(false)
    }
    /*
    fn print(&mut self) {
        const R: isize = 5;
        // for z in -R..=R {
        for z in -1..=1 {
            for i in -R..=R {
                for j in -R..=R {
                    if *self.get_entry((z, i, j)) {
                        print!("#");
                    // print!("{:?}, ", (z, i, j));
                    } else {
                        print!(".");
                    }
                }
                println!();
            }
            println!();
        }
    }
     */
}
