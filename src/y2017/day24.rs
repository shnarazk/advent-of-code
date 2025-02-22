//! <https://adventofcode.com/2017/day/24>
use crate::{
    framework::{AdventOfCode, ParseError, aoc},
    parser,
};

#[derive(Debug, Default, Eq, PartialEq)]
struct Bridge {
    link: Vec<usize>,
    open_end: usize,
}

impl Bridge {
    fn extends(&self, link_id: usize, open_end: usize) -> Bridge {
        let mut link = self.link.clone();
        link.push(link_id);
        Bridge { link, open_end }
    }
}

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<(usize, usize)>,
}

#[aoc(2017, 24)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, input: &str) -> Result<(), ParseError> {
        for l in input.lines() {
            let v = parser::to_usizes(l, &['/'])?;
            self.line.push((v[0], v[1]));
        }
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        self.maximize_bridge(Bridge::default())
    }
    fn part2(&mut self) -> Self::Output2 {
        self.maximize_bridge2(Bridge::default()).1
    }
}

impl Puzzle {
    fn maximize_bridge(&self, bridge: Bridge) -> usize {
        let mut value: usize = 0;
        for (i, link) in self.line.iter().enumerate() {
            if bridge.link.contains(&i) {
                continue;
            }
            if bridge.open_end == link.0 {
                value = value.max(self.maximize_bridge(bridge.extends(i, link.1)));
            } else if bridge.open_end == link.1 {
                value = value.max(self.maximize_bridge(bridge.extends(i, link.0)));
            }
        }
        if value == 0 {
            bridge
                .link
                .iter()
                .map(|i| self.line[*i].0 + self.line[*i].1)
                .sum::<usize>()
        } else {
            value
        }
    }
    fn maximize_bridge2(&self, bridge: Bridge) -> (usize, usize) {
        let mut value = (0, 0);
        for (i, link) in self.line.iter().enumerate() {
            if bridge.link.contains(&i) {
                continue;
            }
            if bridge.open_end == link.0 {
                value = value.max(self.maximize_bridge2(bridge.extends(i, link.1)));
            } else if bridge.open_end == link.1 {
                value = value.max(self.maximize_bridge2(bridge.extends(i, link.0)));
            }
        }
        if value == (0, 0) {
            (
                bridge.link.len(),
                bridge
                    .link
                    .iter()
                    .map(|i| self.line[*i].0 + self.line[*i].1)
                    .sum::<usize>(),
            )
        } else {
            value
        }
    }
}
