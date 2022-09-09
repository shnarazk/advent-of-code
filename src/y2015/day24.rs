//! <https://adventofcode.com/2015/day/24>
use {
    crate::framework::{aoc, AdventOfCode, ParseError},
    std::{cmp::Reverse, collections::BinaryHeap},
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<usize>,
}

#[aoc(2015, 24)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.line.push(block.parse::<usize>()?);
        Ok(())
    }
    fn after_insert(&mut self) {
        dbg!(self.line.iter().sum::<usize>() / 3);
    }
    fn part1(&mut self) -> Self::Output1 {
        let target: usize = self.line.iter().sum::<usize>() / 3;
        // the number of packages in 29.
        type Item = (usize, usize, usize, usize, [bool; 29]);
        let mut to_visit: BinaryHeap<Reverse<Item>> = BinaryHeap::new();
        to_visit.push(Reverse((self.line.len(), 0, 1, 0, [false; 29])));
        while let Some(Reverse((_, len, qe, sum, bag))) = to_visit.pop() {
            if sum == target {
                println!(
                    "{:?}(QE = {:>3})",
                    bag.iter()
                        .zip(self.line.iter())
                        .filter(|(u, _)| **u)
                        .map(|(_, p)| p)
                        .collect::<Vec<_>>(),
                    qe
                );
                return qe;
            }
            let max_remaining_packet: usize = bag
                .iter()
                .zip(self.line.iter())
                .map(|(u, p)| (!u as usize) * p)
                .max()
                .unwrap();
            let l1 = len + 1;
            for (j, p) in self
                .line
                .iter()
                .enumerate()
                .filter(|(i, p)| !bag[*i] && sum + *p <= target)
            {
                let mut new_bag = bag;
                new_bag[j] = true;
                let estimate: usize = (target - sum - p) / max_remaining_packet;
                to_visit.push(Reverse((l1 + estimate, l1, qe * p, sum + p, new_bag)));
            }
        }
        0
    }
    fn part2(&mut self) -> Self::Output2 {
        self.line.reverse();
        let noptions = self.line.len();
        let mut test = 0;
        let target: usize = self.line.iter().sum::<usize>() / 4;
        let mut bag: Vec<(usize, usize, [bool; 29], usize)> = vec![(0, 1, [false; 29], 0)];
        while let Some(smallest) = bag.iter().min() {
            // smallest.3 = false;
            let len = smallest.0;
            let qe = smallest.1;
            let sum = smallest
                .2
                .iter()
                .enumerate()
                .filter(|(_, b)| **b)
                .map(|(i, _)| self.line[i])
                .sum::<usize>();
            if test < sum {
                println!("{}/{} (QE={})", sum, len, qe);
                test = sum;
            }
            if sum == target {
                println!(
                    "{:?}(QE = {:>3})",
                    smallest
                        .2
                        .iter()
                        .enumerate()
                        .filter(|(_, b)| **b)
                        .map(|(i, _)| self.line[i])
                        .collect::<Vec<_>>(),
                    qe
                );
                return qe;
            }
            // if 5 <= len { continue; }
            let s = *smallest;
            bag.retain(|k| *k != s);
            for k in s.3..noptions {
                if s.2[k] || target < sum + self.line[k] {
                    continue;
                }
                let mut new = s;
                new.0 += 1;
                new.1 *= self.line[k];
                new.2[k] = true;
                new.3 = k + 1;
                bag.push(new);
            }
        }
        0
    }
}
