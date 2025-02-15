//! <https://adventofcode.com/2018/day/12>
use {
    crate::framework::{aoc, AdventOfCode, ParseError},
    std::collections::{HashMap, HashSet},
};

type Rules = HashMap<Vec<bool>, bool>;

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Puzzle {
    line: Vec<bool>,
    rules: Rules,
}

mod parser {
    use {
        super::Rules,
        std::collections::HashMap,
        winnow::{
            ascii::newline,
            combinator::{alt, repeat, separated, seq},
            ModalResult, Parser,
        },
    };

    fn parse_data(s: &mut &str) -> ModalResult<Vec<bool>> {
        seq!(_: "initial state: ", repeat(1.., alt(('.', '#'))))
            .map(|(chars,): (Vec<char>,)| chars.iter().map(|c| *c == '#').collect())
            .parse_next(s)
    }

    fn parse_rule(s: &mut &str) -> ModalResult<(Vec<bool>, bool)> {
        seq!(repeat(5, alt(('.', '#'))), _: " => ", alt(('.', '#')))
            .map(|(chars, c): (Vec<char>, char)| {
                (
                    chars.iter().map(|c| *c == '#').collect::<Vec<bool>>(),
                    c == '#',
                )
            })
            .parse_next(s)
    }

    pub fn parse(s: &mut &str) -> ModalResult<(Vec<bool>, Rules)> {
        seq!(
            parse_data, _: (newline, newline), separated(1.., parse_rule, newline)
        )
        .map(|(data, rules): (Vec<bool>, Vec<(Vec<bool>, bool)>)| {
            (
                data,
                rules.into_iter().collect::<HashMap<Vec<bool>, bool>>(),
            )
        })
        .parse_next(s)
    }
}

#[aoc(2018, 12)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, input: String) -> Result<String, ParseError> {
        let (data, rules) = parser::parse(&mut input.as_str())?;
        self.line = data;
        self.rules = rules;
        Self::parsed()
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
        // println!();
        for _g in 1..=20 {
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
        let mut gen: HashSet<isize> = HashSet::new();
        let mut new_gen: HashSet<isize> = HashSet::new();
        for (i, b) in self.line.iter().enumerate() {
            if *b {
                gen.insert(i as isize);
            }
        }
        // print!(" 0: ");
        // for i in -10..140 {
        //     print!("{}", if gen.contains(&i) { '#' } else { '.' },);
        // }
        // println!();
        // It's glider.
        for _g in 1..=90 {
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
            // for i in -10..140 {
            //     print!("{}", if gen.contains(&i) { '#' } else { '.' },);
            // }
            // println!();
        }
        let remain = 50000000000 - 90;
        gen.iter().sum::<isize>() as usize + gen.len() * remain
    }
}
