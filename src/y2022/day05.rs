//! <https://adventofcode.com/2022/day/5>
use {
    crate::{
        framework::{aoc_at, AdventOfCode, ParseError},
        regex,
    },
    std::collections::HashMap,
};

#[derive(Debug, Default, Eq, PartialEq)]
pub struct Puzzle {
    line: Vec<(usize, usize, usize)>,
    stacks: HashMap<usize, Vec<char>>,
}

#[aoc_at(2022, 5)]
impl AdventOfCode for Puzzle {
    type Output1 = String;
    type Output2 = String;
    const DELIMITER: &'static str = "\n";
    fn parse(&mut self, input: String) -> Result<String, ParseError> {
        let mut num_stack = 0;
        let parser = regex!(r"^((.+\n)+)\n((.+\n)+)$");
        let segment = parser.captures(&input).ok_or(ParseError)?;
        for (i, line) in segment[1].split('\n').enumerate() {
            let chs = line.chars().collect::<Vec<char>>();
            if !chs.contains(&'[') {
                break;
            }
            if i == 0 {
                num_stack = (line.len() + 1) / 4;
            }
            for n in 1..=num_stack {
                let ch = chs[4 * (n - 1) + 1];
                if ch == ' ' {
                    continue;
                }
                self.stacks.entry(n).or_default().push(ch);
            }
        }
        Ok(segment[3].to_string())
    }
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        let parser = regex!(r"^move (\d+) from (\d+) to (\d+)$");
        let segment = parser.captures(block).ok_or(ParseError)?;
        self.line.push((
            segment[1].parse::<usize>()?,
            segment[2].parse::<usize>()?,
            segment[3].parse::<usize>()?,
        ));
        Ok(())
    }
    fn end_of_data(&mut self) {
        for st in self.stacks.values_mut() {
            st.reverse();
        }
        // dbg!(&self.stacks);
        // dbg!(&self.line);
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
            // dbg!(&stacks);
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
