//! <https://adventofcode.com/2022/day/5>
use {
    crate::{
        array::rotate_clockwise,
        framework::{AdventOfCode, ParseError, aoc_at},
        parser::parse_usize,
    },
    std::collections::HashMap,
    winnow::{
        ModalResult, Parser,
        ascii::{alpha1, newline, space1},
        combinator::{alt, separated, seq},
    },
};

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Puzzle {
    line: Vec<(usize, usize, usize)>,
    stacks: HashMap<usize, Vec<char>>,
}

fn parse_optional_cell(s: &mut &str) -> ModalResult<Option<char>> {
    let (x,) = alt((seq!(_:"[", alpha1, _: "]"), seq!(_:" ", " ", _:" "))).parse_next(s)?;
    if x == " " {
        Ok(None)
    } else {
        Ok(Some(x.chars().next().unwrap()))
    }
}

fn parse_config_line(s: &mut &str) -> ModalResult<Vec<Option<char>>> {
    separated(1.., parse_optional_cell, " ").parse_next(s)
}

fn parse_config_ids(s: &mut &str) -> ModalResult<()> {
    separated(1.., space1, parse_usize).parse_next(s)
}

fn parse_config(s: &mut &str) -> ModalResult<Vec<Vec<Option<char>>>> {
    seq!(separated(1.., parse_config_line, newline), _: newline, _: parse_config_ids)
        .map(|(t,)| t)
        .parse_next(s)
}

fn parse_move(s: &mut &str) -> ModalResult<(usize, usize, usize)> {
    seq!(_: "move ", parse_usize, _: " from ", parse_usize, _: " to ", parse_usize).parse_next(s)
}

fn parse_moves(s: &mut &str) -> ModalResult<Vec<(usize, usize, usize)>> {
    separated(1.., parse_move, newline).parse_next(s)
}

#[allow(clippy::type_complexity)]
fn parse(s: &mut &str) -> ModalResult<(Vec<Vec<Option<char>>>, Vec<(usize, usize, usize)>)> {
    seq!(parse_config, _: newline, _: newline, parse_moves).parse_next(s)
}

#[aoc_at(2022, 5)]
impl AdventOfCode for Puzzle {
    type Output1 = String;
    type Output2 = String;
    fn prepare(&mut self, mut input: &str) -> Result<(), ParseError> {
        let (mc, moves) = parse(&mut input)?;
        let maze_config = rotate_clockwise(mc);
        for (n, config) in maze_config.iter().enumerate() {
            let stack = config.iter().flatten().cloned().collect::<Vec<_>>();
            self.stacks.insert(n + 1, stack);
        }
        self.line = moves;
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        let Puzzle { line, stacks } = self;
        for (amount, from, to) in line.iter() {
            for _ in 0..*amount {
                let Some(x) = stacks.get_mut(from).unwrap().pop() else {
                    panic!();
                };
                stacks.get_mut(to).unwrap().push(x);
            }
        }
        (1..=stacks.len())
            .map(|i| stacks.get(&i).unwrap().last().unwrap())
            .collect::<String>()
    }
    fn part2(&mut self) -> Self::Output2 {
        let Puzzle { line, stacks } = self;
        for (amount, from, to) in line.iter() {
            let mut tmp = Vec::new();
            for _ in 0..*amount {
                let Some(x) = stacks.get_mut(from).unwrap().pop() else {
                    panic!();
                };
                tmp.push(x);
            }
            while let Some(x) = tmp.pop() {
                stacks.get_mut(to).unwrap().push(x);
            }
        }
        (1..=stacks.len())
            .map(|i| stacks.get(&i).unwrap().last().unwrap())
            .collect::<String>()
    }
}
