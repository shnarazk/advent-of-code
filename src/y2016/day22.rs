//! <https://adventofcode.com/2016/day/22>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]

use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::neighbors,
        line_parser, regex,
    },
    std::collections::{binary_heap::BinaryHeap, HashSet},
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<(usize, usize, usize, usize, usize, usize)>,
}

#[aoc(2016, 22)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn header(&mut self, input: String) -> Result<String, ParseError> {
        let parser = regex!(r"^.+\n.+\n((.|\n)+)$");
        let segment = parser.captures(&input).ok_or(ParseError)?;
        Ok(segment[1].to_string())
    }
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        let parser = regex!(r"/dev/grid/node-x(\d+)-y(\d+) +(\d+)T +(\d+)T +(\d+)T +(\d+)%$");
        let segment = parser.captures(block).ok_or(ParseError)?;
        self.line.push((
            segment[1].parse::<usize>()?,
            segment[2].parse::<usize>()?,
            segment[3].parse::<usize>()?,
            segment[4].parse::<usize>()?,
            segment[5].parse::<usize>()?,
            segment[6].parse::<usize>()?,
        ));
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        self.line.sort_unstable_by_key(|line| line.4);
        let n = self.line.len();
        let mut count = 0;
        for (i, dev) in self.line.iter().enumerate() {
            for (j, other) in self.line.iter().enumerate() {
                if 0 < dev.3 && i != j && dev.3 <= other.4 {
                    count += 1;
                }
            }
        }
        count
    }
    fn part2(&mut self) -> Self::Output2 {
        type State = Vec<usize>;
        let mut to_visit: BinaryHeap<(usize, State)> = BinaryHeap::new();
        let mut visited: HashSet<State> = HashSet::new();
        let init = self.line.iter().map(|site| site.3).collect::<Vec<usize>>();
        to_visit.push((0, init));
        while let Some(state) = to_visit.pop() {
            for (i, used) in state.1.iter().enumerate() {
                if *used == 0 {
                    dbg!(i);
                }
            }
            visited.insert(state.1);
        }
        0
    }
}

#[cfg(feature = "y2016")]
#[cfg(test)]
mod test {
    use {
        super::*,
        crate::framework::{Answer, Description},
    };

    // #[test]
    // fn test_part1() {
    //     assert_eq!(
    //         Puzzle::solve(Description::TestData("".to_string()), 1),
    //         Answer::Part1(0)
    //     );
    // }
}
