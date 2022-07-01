//! <https://adventofcode.com/2019/day/10>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::neighbors,
        math::gcd,
    },
    std::collections::HashSet,
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Vec<bool>>,
}

#[aoc(2019, 10)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.line
            .push(block.chars().map(|c| c == '#').collect::<Vec<bool>>());
        Ok(())
    }
    fn after_insert(&mut self) {
        let height = self.line.len();
        let width = self.line[0].len();
        dbg!(height, width);
    }
    fn part1(&mut self) -> Self::Output1 {
        let height = self.line.len();
        let width = self.line[0].len();
        let mut best = (0, 0);
        let mut max_visible = 0;
        for (j, l) in self.line.iter().enumerate() {
            for (i, p) in l.iter().enumerate() {
                if !self.at(j, i) {
                    continue;
                }
                let mut visible: HashSet<(isize, isize)> = HashSet::new();
                for (jj, ll) in self.line.iter().enumerate() {
                    for (ii, pp) in l.iter().enumerate() {
                        if self.at(jj, ii) {
                            let dy = jj as isize - j as isize;
                            let dx = ii as isize - i as isize;
                            match (dy, dx) {
                                (0, 0) => (),
                                (0, _) => {
                                    visible.insert((0, dx.signum()));
                                }
                                (_, 0) => {
                                    visible.insert((dy.signum(), 0));
                                }
                                _ => {
                                    let factor = gcd(dy.unsigned_abs(), dx.unsigned_abs()) as isize;
                                    visible.insert((dy / factor, dx / factor));
                                }
                            }
                        }
                    }
                }
                let n = visible.len();
                if max_visible < n {
                    max_visible = n;
                    best = (j, i);
                }
            }
        }
        dbg!(&best);
        max_visible
    }
    fn part2(&mut self) -> Self::Output2 {
        0
    }
}

impl Puzzle {
    fn at(&self, y: usize, x: usize) -> bool {
        self.line[y][x]
    }
}

#[cfg(feature = "y2019")]
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
