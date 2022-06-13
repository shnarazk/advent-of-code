//! <https://adventofcode.com/2016/day/24>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::neighbors4,
        line_parser, regex,
    },
    std::collections::{HashMap, VecDeque},
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Vec<bool>>,
    targets: Vec<(usize, usize)>,
    cost: Vec<Vec<usize>>,
    height: usize,
    width: usize,
}

#[aoc(2016, 24)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        let mut line = Vec::new();
        let j = self.line.len();
        for (i, c) in block.chars().enumerate() {
            if c.is_ascii_digit() {
                self.targets.push((j, i));
                line.push(true);
            } else {
                line.push(c == '.');
            }
        }
        self.line.push(line);
        Ok(())
    }
    fn after_insert(&mut self) {
        self.height = self.line.len();
        self.width = self.line[0].len();
        // Add the start point
        self.targets.sort();
        if (1, 1) != self.targets[0] {
            self.targets.insert(0, (1, 1));
        }
        let targets = self.targets.len();
        for j in 0..targets {
            self.cost
                .push((0..targets).map(|_| usize::MAX).collect::<Vec<usize>>());
        }
        'next_target: for (k, start) in self.targets.iter().enumerate() {
            let mut cost: HashMap<(usize, usize), usize> = HashMap::new();
            for (j, i) in self.targets.iter() {
                cost.insert((*j, *i), usize::MAX);
            }
            let mut to_check: VecDeque<(usize, usize)> = VecDeque::new();
            let mut found = 1;
            cost.insert(*start, 0);
            self.cost[k][k] = 0;
            to_check.push_back(*start);
            while let Some(p) = to_check.pop_front() {
                let c = cost.get(&p).unwrap() + 1;
                for (j, i) in neighbors4(p.0, p.1, self.height, self.width) {
                    if !self.line[j][i] {
                        continue;
                    }
                    if let Some(w) = cost.get(&(j, i)) {
                        if *w != usize::MAX {
                            continue;
                        }
                        found += 1;
                        for (l, goal) in self.targets.iter().enumerate() {
                            if goal.0 == j && goal.1 == i {
                                self.cost[k][l] = c;
                                self.cost[l][k] = c;
                            }
                        }
                        if found == targets {
                            continue 'next_target;
                        }
                    }
                    cost.insert((j, i), c);
                    to_check.push_back((j, i));
                }
            }
        }
        for (i, l) in self.cost.iter().enumerate() {
            for d in l.iter() {
                print!("{d:>4},");
            }
            println!("\t{:?}", self.targets[i]);
        }
    }
    fn part1(&mut self) -> Self::Output1 {
        0
    }
    fn part2(&mut self) -> Self::Output2 {
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
