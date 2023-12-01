//! <https://adventofcode.com/2017/day/24>
use crate::{
    framework::{aoc, AdventOfCode, ParseError},
    line_parser,
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Bridge {
    link: Vec<usize>,
    open_end: usize,
    weight: usize,
}

impl Bridge {
    fn extends(&self, link_id: usize, connecting_end: usize, open_end: usize) -> Bridge {
        let mut link = self.link.clone();
        link.push(link_id);
        Bridge {
            link,
            open_end,
            weight: self.weight + connecting_end + open_end,
        }
    }
}

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<(usize, usize)>,
}

#[aoc(2017, 24)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        let v = line_parser::to_usizes(block, '/')?;
        self.line.push((v[0], v[1]));
        Ok(())
    }
    fn end_of_data(&mut self) {
        dbg!(&self.line.len());
    }
    fn part1(&mut self) -> Self::Output1 {
        let init = Bridge::default();
        self.maximize_bridge(init)
    }
    fn part2(&mut self) -> Self::Output2 {
        self.maximize_bridge2(Bridge::default()).1
    }
}

impl Puzzle {
    fn maximize_bridge(&self, bridge: Bridge) -> usize {
        let mut value: usize = bridge.weight;
        for (i, link) in self.line.iter().enumerate() {
            if bridge.link.contains(&i) {
                continue;
            }
            if bridge.open_end == link.0 {
                value = value.max(self.maximize_bridge(bridge.extends(i, link.0, link.1)));
            } else if bridge.open_end == link.1 {
                value = value.max(self.maximize_bridge(bridge.extends(i, link.1, link.0)));
            }
        }
        value
    }
    fn maximize_bridge2(&self, bridge: Bridge) -> (usize, usize) {
        let mut value: (usize, usize) = (bridge.link.len(), bridge.weight);
        for (i, link) in self.line.iter().enumerate() {
            if bridge.link.contains(&i) {
                continue;
            }
            if bridge.open_end == link.0 {
                value = value.max(self.maximize_bridge2(bridge.extends(i, link.0, link.1)));
            } else if bridge.open_end == link.1 {
                value = value.max(self.maximize_bridge2(bridge.extends(i, link.1, link.0)));
            }
        }
        value
    }
}
