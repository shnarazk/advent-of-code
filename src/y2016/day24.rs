//! <https://adventofcode.com/2016/day/24>
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::neighbors4,
    },
    std::{
        cmp::Reverse,
        collections::{BinaryHeap, HashMap, VecDeque},
    },
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Vec<bool>>,
    targets: Vec<(usize, (usize, usize))>,
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
                self.targets.push(((c as u8 - b'0') as usize, (j, i)));
                line.push(true);
            } else {
                line.push(c == '.');
            }
        }
        self.line.push(line);
        Ok(())
    }
    fn end_of_data(&mut self) {
        self.height = self.line.len();
        self.width = self.line[0].len();
        self.targets.sort_unstable();
        let targets = self.targets.len();
        for _ in 0..targets {
            self.cost
                .push((0..targets).map(|_| usize::MAX).collect::<Vec<usize>>());
        }
        'next_target: for (k, start) in self.targets.iter() {
            let mut cost: HashMap<(usize, usize), usize> = HashMap::new();
            for (_, p) in self.targets.iter() {
                cost.insert(*p, usize::MAX);
            }
            let mut to_check: VecDeque<(usize, usize)> = VecDeque::new();
            let mut found = 1;
            cost.insert(*start, 0);
            self.cost[*k][*k] = 0;
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
                        for (l, goal) in self.targets.iter() {
                            if goal.0 == j && goal.1 == i {
                                self.cost[*k][*l] = c;
                                self.cost[*l][*k] = c;
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
        // for (i, l) in self.cost.iter().enumerate() {
        //     for d in l.iter() {
        //         print!("{d:>4},");
        //     }
        //     println!("\t{:?}", self.targets[i]);
        // }
    }
    fn part1(&mut self) -> Self::Output1 {
        let goal = self.targets.len();
        let mut pathes: BinaryHeap<Reverse<(usize, Vec<usize>)>> = BinaryHeap::new();
        let mut least = usize::MAX;
        pathes.push(Reverse((0, vec![0])));
        while let Some(Reverse((cost, path))) = pathes.pop() {
            if path.len() == goal {
                if cost < least {
                    least = cost;
                }
                continue;
            }
            for i in 0..goal {
                if path.contains(&i) {
                    continue;
                }
                let lst = *path.last().unwrap();
                let mut p = path.clone();
                p.push(i);
                pathes.push(Reverse((cost + self.cost[lst][i], p)))
            }
        }
        least
    }
    fn part2(&mut self) -> Self::Output2 {
        let goal = self.targets.len();
        let mut pathes: BinaryHeap<Reverse<(usize, Vec<usize>)>> = BinaryHeap::new();
        let mut least = usize::MAX;
        pathes.push(Reverse((0, vec![0])));
        while let Some(Reverse((cost, path))) = pathes.pop() {
            if path.len() == goal {
                let lst = *path.last().unwrap();
                let c = cost + self.cost[lst][0];
                if c < least {
                    least = c;
                }
                continue;
            }
            for i in 0..goal {
                if path.contains(&i) {
                    continue;
                }
                let lst = *path.last().unwrap();
                let mut p = path.clone();
                p.push(i);
                pathes.push(Reverse((cost + self.cost[lst][i], p)))
            }
        }
        least
    }
}
