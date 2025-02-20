//! <https://adventofcode.com/2018/day/12>
use {
    crate::framework::{AdventOfCode, ParseError, aoc},
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
            ModalResult, Parser,
            ascii::newline,
            combinator::{alt, repeat, separated, seq},
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
    fn parse(&mut self, mut input: &str) -> Result<(), ParseError> {
        let (data, rules) = parser::parse(&mut input)?;
        self.line = data;
        self.rules = rules;
        Self::parsed()
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut cur_gen: HashSet<isize> = HashSet::new();
        let mut new_gen: HashSet<isize> = HashSet::new();
        for (i, b) in self.line.iter().enumerate() {
            if *b {
                cur_gen.insert(i as isize);
            }
        }
        // print!(" 0: ");
        // for i in -4..34 {
        //     print!("{}", if gen.contains(&i) { '#' } else { '.' },);
        // }
        // println!();
        for _g in 1..=20 {
            let left: isize = *cur_gen.iter().min().unwrap_or(&0);
            let right: isize = *cur_gen.iter().max().unwrap_or(&0);
            for i in left - 4..=right + 4 {
                if let Some(true) = self.rules.get(&vec![
                    cur_gen.contains(&(i - 2)),
                    cur_gen.contains(&(i - 1)),
                    cur_gen.contains(&i),
                    cur_gen.contains(&(i + 1)),
                    cur_gen.contains(&(i + 2)),
                ]) {
                    new_gen.insert(i);
                }
            }
            std::mem::swap(&mut cur_gen, &mut new_gen);
            new_gen.clear();
            // print!("{g:>2}: ");
            // for i in left - 4..right + 4 {
            //     print!("{}", if gen.contains(&i) { '#' } else { '.' },);
            // }
            // println!();
        }
        cur_gen.iter().sum::<isize>() as usize
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut cur_gen: HashSet<isize> = HashSet::new();
        let mut new_gen: HashSet<isize> = HashSet::new();
        for (i, b) in self.line.iter().enumerate() {
            if *b {
                cur_gen.insert(i as isize);
            }
        }
        // print!(" 0: ");
        // for i in -10..140 {
        //     print!("{}", if gen.contains(&i) { '#' } else { '.' },);
        // }
        // println!();
        // It's glider.
        for _g in 1..=90 {
            let left: isize = *cur_gen.iter().min().unwrap_or(&0);
            let right: isize = *cur_gen.iter().max().unwrap_or(&0);
            for i in left - 4..=right + 4 {
                if let Some(true) = self.rules.get(&vec![
                    cur_gen.contains(&(i - 2)),
                    cur_gen.contains(&(i - 1)),
                    cur_gen.contains(&i),
                    cur_gen.contains(&(i + 1)),
                    cur_gen.contains(&(i + 2)),
                ]) {
                    new_gen.insert(i);
                }
            }
            std::mem::swap(&mut cur_gen, &mut new_gen);
            new_gen.clear();
            // print!("{g:>2}: ");
            // for i in -10..140 {
            //     print!("{}", if gen.contains(&i) { '#' } else { '.' },);
            // }
            // println!();
        }
        let remain = 50000000000 - 90;
        cur_gen.iter().sum::<isize>() as usize + cur_gen.len() * remain
    }
}
