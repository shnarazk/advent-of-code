//! <https://adventofcode.com/2018/day/12>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::neighbors,
        line_parser, regex,
    },
    std::collections::{HashMap, HashSet},
};

#[derive(Debug, Default, Eq, PartialEq)]
pub struct Puzzle {
    line: Vec<bool>,
    rules: HashMap<Vec<bool>, bool>,
}

#[aoc(2018, 12)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn header(&mut self, input: String) -> Result<String, ParseError> {
        let parser = regex!(r"^initial state: (.+)\n\n((.|\n)+)$");
        let segment = parser.captures(&input).ok_or(ParseError)?;
        self.line = segment[1].chars().map(|c| c == '#').collect::<Vec<bool>>();
        Ok(segment[2].to_string())
    }
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        let parser = regex!(r"^([.#]+) => ([.#]+)$");
        let segment = parser.captures(block).ok_or(ParseError)?;
        self.rules.insert(
            segment[1].chars().map(|c| c == '#').collect::<Vec<bool>>(),
            &segment[2] == "#",
        );
        Ok(())
    }
    fn after_insert(&mut self) {
        dbg!(&self.line.len());
        dbg!(&self.rules.len());
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut gen: HashSet<isize> = HashSet::new();
        let mut new_gen: HashSet<isize> = HashSet::new();
        for (i, b) in self.line.iter().enumerate() {
            if *b {
                gen.insert(i as isize);
            }
        }
        // print!(" 0: ");
        // for i in -4..34 {
        //     print!("{}", if gen.contains(&i) { '#' } else { '.' },);
        // }
        println!();
        for g in 1..=20 {
            let left: isize = *gen.iter().min().unwrap_or(&0);
            let right: isize = *gen.iter().max().unwrap_or(&0);
            for i in left - 4..=right + 4 {
                if let Some(true) = self.rules.get(&vec![
                    gen.contains(&(i - 2)),
                    gen.contains(&(i - 1)),
                    gen.contains(&i),
                    gen.contains(&(i + 1)),
                    gen.contains(&(i + 2)),
                ]) {
                    new_gen.insert(i);
                }
            }
            std::mem::swap(&mut gen, &mut new_gen);
            new_gen.clear();
            // print!("{g:>2}: ");
            // for i in left - 4..right + 4 {
            //     print!("{}", if gen.contains(&i) { '#' } else { '.' },);
            // }
            // println!();
        }
        gen.iter().sum::<isize>() as usize
    }
    fn part2(&mut self) -> Self::Output2 {
        0
    }
}
