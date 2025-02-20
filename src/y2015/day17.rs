//! <https://adventofcode.com/2015/day/17>
use crate::framework::{aoc, AdventOfCode, ParseError};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<usize>,
}

#[aoc(2015, 17)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn parse_block(&mut self, block: &str) -> Result<(), ParseError> {
        self.line.push(block.parse::<usize>()?);
        Ok(())
    }
    fn end_of_data(&mut self) {
        // dbg!(&self.line);
    }
    fn part1(&mut self) -> Self::Output1 {
        self.patterns_for(150)
    }
    fn part2(&mut self) -> Self::Output2 {
        self.minimize(150)
    }
}

impl Puzzle {
    fn patterns_for(&self, target: usize) -> usize {
        let mut memo: Vec<usize> = vec![0; target + 1];
        memo[0] = 1;
        for l in self.line.iter() {
            for i in (0..=target).rev() {
                let new_volume = i + l;
                if new_volume <= target {
                    memo[new_volume] += memo[i];
                }
            }
        }
        // let mut containers = self.line.clone();
        // containers.sort_unstable();
        // println!("{:?}", &containers);
        // println!("{:?}", &memo[..10]);
        memo[target]
    }
    fn minimize(&self, target: usize) -> usize {
        type Solution = Vec<usize>;
        let mut memo: Vec<Vec<Solution>> = Vec::new();
        memo.resize(target + 1, Vec::new());
        memo[0].push(Vec::new());
        for l in self.line.iter() {
            for i in (0..=target).rev() {
                let new_volume = i + l;
                if new_volume <= target {
                    let mut copy: Vec<Solution> = memo[i]
                        .iter()
                        .cloned()
                        .map(|mut solution| {
                            solution.push(*l);
                            solution
                        })
                        .collect::<Vec<_>>();
                    memo[new_volume].append(&mut copy);
                }
            }
        }
        let min = memo[target]
            .iter()
            .map(|solution| solution.len())
            .min()
            .unwrap();
        memo[target]
            .iter()
            .filter(|solution| solution.len() == min)
            .count()
    }
}
