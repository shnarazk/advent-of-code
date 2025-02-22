//! <https://adventofcode.com/2017/day/12>
use {
    crate::framework::{AdventOfCode, ParseError, aoc},
    std::collections::{HashMap, HashSet},
};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<(usize, Vec<usize>)>,
}

mod parser {
    use {
        crate::parser::parse_usize,
        winnow::{
            ModalResult, Parser,
            ascii::newline,
            combinator::{separated, seq},
        },
    };

    fn parse_line(s: &mut &str) -> ModalResult<(usize, Vec<usize>)> {
        seq!(parse_usize, _: " <-> ", separated(1.., parse_usize, ", ")).parse_next(s)
    }

    pub fn parse(s: &mut &str) -> ModalResult<Vec<(usize, Vec<usize>)>> {
        separated(1.., parse_line, newline).parse_next(s)
    }
}

#[aoc(2017, 12)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, mut input: &str) -> Result<(), ParseError> {
        self.line = parser::parse(&mut input)?;
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut map: HashMap<usize, Vec<usize>> = HashMap::new();
        for (from, tos) in self.line.iter() {
            map.insert(*from, tos.clone());
        }
        let mut linked: HashSet<usize> = HashSet::new();
        linked.insert(0);
        let mut to_visit: Vec<usize> = vec![0];
        while let Some(n) = to_visit.pop() {
            if let Some(tos) = map.get(&n) {
                for to in tos.iter() {
                    if !linked.contains(to) {
                        linked.insert(*to);
                        to_visit.push(*to);
                    }
                }
            }
        }
        linked.len()
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut n_groups = 0;
        let mut map: HashMap<usize, Vec<usize>> = HashMap::new();
        for (from, tos) in self.line.iter() {
            map.insert(*from, tos.clone());
        }
        let mut found: HashSet<usize> = HashSet::new();
        while let Some(start) = (0..self.line.len()).find(|i| !found.contains(i)) {
            n_groups += 1;
            found.insert(start);
            let mut to_visit: Vec<usize> = vec![start];
            while let Some(n) = to_visit.pop() {
                if let Some(tos) = map.get(&n) {
                    for to in tos.iter() {
                        if !found.contains(to) {
                            found.insert(*to);
                            to_visit.push(*to);
                        }
                    }
                }
            }
        }
        n_groups
    }
}
