//! <https://adventofcode.com/2016/day/10>
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        regex,
    },
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

#[aoc(2016, 10)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        let parser1 =
            regex!(r"bot (\d+) gives low to (bot|output) (\d+) and high to (bot|output) (\d+)");
        let parser2 = regex!(r"value (\d+) goes to bot (\d+)");
        if let Some(segment) = parser1.captures(block) {
            let id1 = segment[3].parse::<usize>()?;
            let id2 = segment[5].parse::<usize>()?;
            let dest1 = if &segment[2] == "bot" {
                Destination::Bot(id1)
            } else {
                Destination::Output(id1)
            };
            let dest2 = if &segment[4] == "bot" {
                Destination::Bot(id2)
            } else {
                Destination::Output(id2)
            };
            self.line
                .push(Op::Wire(segment[1].parse::<usize>()?, dest1, dest2));
            return Ok(());
        }
        if let Some(segment) = parser2.captures(block) {
            self.line.push(Op::Val(
                segment[1].parse::<usize>()?,
                segment[2].parse::<usize>()?,
            ));
            return Ok(());
        }
        Err(ParseError)
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
