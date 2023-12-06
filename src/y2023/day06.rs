//! <https://adventofcode.com/2023/day/6>
use crate::{
    framework::{aoc, AdventOfCode, ParseError},
    line_parser,
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    index: usize,
    line: Vec<Vec<usize>>,
    setting1: Vec<(usize, usize)>,
    setting2: (usize, usize),
}

#[aoc(2023, 6)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        let s = block.split(':').nth(1).unwrap().trim();
        self.line.push(line_parser::to_usizes(s, ' ').unwrap());
        Ok(())
    }
    fn end_of_data(&mut self) {
        for (i, t) in self.line[0].iter().enumerate() {
            self.setting1.push((*t, self.line[1][i]));
        }
        let s2 = self
            .line
            .iter()
            .map(|vec| {
                let mut s = 0;
                for x in vec.iter() {
                    s = s * 10_usize.pow(x.ilog(10) + 1) + *x;
                }
                s
            })
            .collect::<Vec<_>>();
        self.setting2 = (s2[0], s2[1]);
    }
    fn part1(&mut self) -> Self::Output1 {
        self.setting1
            .iter()
            .map(|(t, d)| (1..*t - 1).filter(|x| *x * (*t - *x) > *d).count())
            .product::<usize>()
    }
    fn part2(&mut self) -> Self::Output2 {
        let (t, d) = self.setting2;
        (1..t - 1).filter(|x| *x * (t - *x) > d).count()
    }
}
