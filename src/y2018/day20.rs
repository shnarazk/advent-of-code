//! <https://adventofcode.com/2018/day/20>
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

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Reg(Vec<u8>);

#[derive(Debug, Eq, Hash, PartialEq)]
enum Rege {
    Run(Vec<u8>),
    Branch(Vec<Rege>),
}

impl Rege {
    fn render(&self) {
        match self {
            Rege::Run(v) => print!("{}", v.iter().map(|c| *c as char).collect::<String>()),
            Rege::Branch(v) => {
                let n = v.len();
                print!("(");
                for (i, r) in v.iter().enumerate() {
                    r.render();
                    if i + 1 < n {
                        print!("|");
                    }
                }
                print!(")");
            }
        }
    }
}

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<u8>,
}

fn parse_to_run(string: &[u8], start: usize) -> Result<(Reg, usize), ParseError> {
    let mut i = start;
    while let Some(c) = string.get(i) {
        if *c == b'$' || *c == b')' || *c == b'(' || *c == b'|' {
            break;
        }
        i += 1;
    }
    Ok((Reg(string[start..i].to_vec()), i))
}

fn parse_to_branch(string: &[u8], start: usize) -> Result<(Rege, usize), ParseError> {
    let mut vec: Vec<Rege> = Vec::new();
    let mut i = start;
    if string.get(start) == Some(&b'(') {
        if let Ok((element, j)) = parse_to_branch(string, i) {
            vec.push(element);
            i = j;
        } else {
        }
    } else if let Ok((element, j)) = parse_to_run(string, i) {
        vec.push(Rege::Run(element.0));
        i = j;
    } else {
    }
    while let Some(c) = string.get(i) {
        // dbg!(*c as char);
        match c {
            b'(' => {
                if let Ok((element, j)) = parse_to_branch(string, i + 1) {
                    vec.push(element);
                    i = j;
                }
            }
            b'|' => {
                i += 1;
                if string.get(i) == Some(&b'(') {
                    if let Ok((element, j)) = parse_to_branch(string, i) {
                        vec.push(element);
                        i = j;
                    }
                } else if string.get(i) == Some(&b')') {
                    vec.push(Rege::Run(Vec::new()));
                } else if let Ok((element, j)) = parse_to_run(string, i) {
                    vec.push(Rege::Run(element.0));
                    i = j;
                } else {
                }
            }
            b')' | b'$' => {
                // i += 2;
                break;
            }
            _ => {
                // dbg!(&string[0..=i].iter().map(|c| *c as char).collect::<String>());
                if let Ok((element, j)) = parse_to_run(string, i) {
                    vec.push(Rege::Run(element.0));
                    i = j;
                }
            }
        }
    }
    Ok((Rege::Branch(vec), i + 1))
}

#[aoc(2018, 20)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        dbg!(block);
        self.line = block.chars().map(|c| c as u8).collect::<Vec<u8>>();
        Ok(())
    }
    fn after_insert(&mut self) {
        // dbg!(&self.line);
    }
    fn part1(&mut self) -> Self::Output1 {
        self.line.push(b')');
        if let Ok((tree, _)) = parse_to_branch(&self.line, 1) {
            tree.render();
        }
        0
    }
    fn part2(&mut self) -> Self::Output2 {
        0
    }
}
