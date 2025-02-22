//! <https://adventofcode.com/2016/day/10>
use {
    crate::framework::{AdventOfCode, ParseError, aoc},
    std::collections::HashMap,
};

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Destination {
    Bot(usize),
    Output(usize),
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Op {
    Wire(usize, Destination, Destination),
    Val(usize, usize),
}

#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
pub struct Puzzle {
    line: Vec<Op>,
}

mod parser {
    use {
        super::*,
        crate::parser::parse_usize,
        winnow::{
            ModalResult, Parser,
            ascii::newline,
            combinator::{alt, separated, seq},
        },
    };
    fn parse_target(s: &mut &str) -> ModalResult<Destination> {
        alt((
            seq!(_: "bot ",  parse_usize).map(|(id,)| Destination::Bot(id)),
            seq!(_: "output ",  parse_usize).map(|(id,)| Destination::Output(id)),
        ))
        .parse_next(s)
    }
    fn parse_op(s: &mut &str) -> ModalResult<Op> {
        alt((
            seq!(_: "bot ", parse_usize, _: " gives low to ", parse_target, _: " and high to ", parse_target).map(|(n, d1, d2)| Op::Wire(n, d1, d2)),
            seq!(_: "value ", parse_usize, _: " goes to bot ", parse_usize)
                .map(|(a, b)| Op::Val(a, b)),
        ))
        .parse_next(s)
    }

    pub fn parse(s: &mut &str) -> ModalResult<Vec<Op>> {
        separated(1.., parse_op, newline).parse_next(s)
    }
}

#[aoc(2016, 10)]
impl AdventOfCode for Puzzle {
    fn prepare(&mut self, mut input: &str) -> Result<(), ParseError> {
        self.line = parser::parse(&mut input)?;
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut map: HashMap<usize, (Destination, Destination)> = HashMap::new();
        for op in self.line.iter() {
            if let Op::Wire(b, d1, d2) = op {
                map.insert(*b, (*d1, *d2));
            }
        }
        let mut output: HashMap<usize, usize> = HashMap::new();
        let mut state: HashMap<usize, (Option<usize>, Option<usize>)> = HashMap::new();
        let mut to_update: Vec<usize> = Vec::new();
        for op in self.line.iter() {
            if let Op::Val(v, b) = op {
                let entry = state.entry(*b).or_insert((None, None));
                match *entry {
                    (None, None) => {
                        entry.0 = Some(*v);
                    }
                    (Some(low), None) if *v <= low => {
                        entry.1 = entry.0;
                        entry.0 = Some(*v);
                        to_update.push(*b);
                    }
                    (Some(_), None) => {
                        entry.1 = Some(*v);
                        to_update.push(*b);
                    }
                    _ => unreachable!(),
                }
            }
        }
        while let Some(b) = to_update.pop() {
            let targets = map.get(&b).unwrap();
            let values = state.get(&b).unwrap();
            for (dist, val) in [(targets.0, values.0), (targets.1, values.1)] {
                let v = val.unwrap();
                match dist {
                    Destination::Output(k) => {
                        output.insert(k, v);
                    }
                    Destination::Bot(b) => {
                        let entry = state.entry(b).or_insert((None, None));
                        match *entry {
                            (None, None) => {
                                entry.0 = Some(v);
                            }
                            (Some(low), None) if v <= low => {
                                entry.1 = entry.0;
                                entry.0 = Some(v);
                                to_update.push(b);
                            }
                            (Some(_), None) => {
                                entry.1 = Some(v);
                                to_update.push(b);
                            }
                            _ => unreachable!(),
                        }
                    }
                }
            }
        }
        for (bot, (c1, c2)) in state.iter() {
            // println!("b{bot}: {c1:?}-{c2:?}");
            if *c1 == Some(17) && *c2 == Some(61) {
                return *bot;
            }
        }
        0
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut map: HashMap<usize, (Destination, Destination)> = HashMap::new();
        for op in self.line.iter() {
            if let Op::Wire(b, d1, d2) = op {
                map.insert(*b, (*d1, *d2));
            }
        }
        let mut output: HashMap<usize, usize> = HashMap::new();
        let mut state: HashMap<usize, (Option<usize>, Option<usize>)> = HashMap::new();
        let mut to_update: Vec<usize> = Vec::new();
        for op in self.line.iter() {
            if let Op::Val(v, b) = op {
                let entry = state.entry(*b).or_insert((None, None));
                match *entry {
                    (None, None) => {
                        entry.0 = Some(*v);
                    }
                    (Some(low), None) if *v <= low => {
                        entry.1 = entry.0;
                        entry.0 = Some(*v);
                        to_update.push(*b);
                    }
                    (Some(_), None) => {
                        entry.1 = Some(*v);
                        to_update.push(*b);
                    }
                    _ => unreachable!(),
                }
            }
        }
        while let Some(b) = to_update.pop() {
            let targets = map.get(&b).unwrap();
            let values = state.get(&b).unwrap();
            for (dist, val) in [(targets.0, values.0), (targets.1, values.1)] {
                let v = val.unwrap();
                match dist {
                    Destination::Output(k) => {
                        output.insert(k, v);
                    }
                    Destination::Bot(b) => {
                        let entry = state.entry(b).or_insert((None, None));
                        match *entry {
                            (None, None) => {
                                entry.0 = Some(v);
                            }
                            (Some(low), None) if v <= low => {
                                entry.1 = entry.0;
                                entry.0 = Some(v);
                                to_update.push(b);
                            }
                            (Some(_), None) => {
                                entry.1 = Some(v);
                                to_update.push(b);
                            }
                            _ => unreachable!(),
                        }
                    }
                }
            }
        }
        output.get(&0).unwrap() * output.get(&1).unwrap() * output.get(&2).unwrap()
    }
}
