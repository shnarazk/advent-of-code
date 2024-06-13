//! <https://adventofcode.com/2018/day/7>
use {
    crate::{
        framework::{aoc_at, AdventOfCode, ParseError},
        regex,
    },
    std::collections::{HashMap, HashSet},
};

#[derive(Debug, Default, Eq, PartialEq)]
struct Worker {
    working: Option<char>,
    finish_at: usize,
}

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<(char, char)>,
}

#[aoc_at(2018, 7)]
impl AdventOfCode for Puzzle {
    type Output1 = String;
    type Output2 = usize;
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        // Step L must be finished before step X can begin.
        let parser = regex!(r"^Step (\w) must be finished before step (\w) can begin.");
        let segment = parser.captures(block).ok_or(ParseError)?;
        self.line.push((
            segment[1].chars().next().unwrap(),
            segment[2].chars().next().unwrap(),
        ));
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut succs: HashMap<char, Vec<char>> = HashMap::new();
        let mut conds: HashMap<char, Vec<char>> = HashMap::new();
        let mut prev: HashMap<char, char> = HashMap::new();
        let mut letters: HashSet<char> = HashSet::new();
        for rel in self.line.iter() {
            letters.insert(rel.0);
            letters.insert(rel.1);
            succs.entry(rel.0).or_default().push(rel.1);
            conds.entry(rel.1).or_default().push(rel.0);
            prev.insert(rel.1, rel.0);
        }
        let mut available: Vec<char> = succs
            .keys()
            .filter(|n| !prev.contains_key(n))
            .copied()
            .collect::<Vec<_>>();
        let mut result: String = String::new();
        loop {
            if available.is_empty() {
                break;
            }
            available.sort();
            let mut c: char = ' ';
            for (i, cand) in available.iter().enumerate() {
                if conds
                    .get(cand)
                    .unwrap_or(&vec![])
                    .iter()
                    .all(|c| result.contains(*c))
                {
                    c = available.remove(i);
                    break;
                }
            }
            if let Some(v) = succs.get(&c) {
                for s in v.iter() {
                    if !available.contains(s) && !result.contains(*s) {
                        available.push(*s);
                    }
                }
            }
            result.push(c);
        }
        result
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut succs: HashMap<char, Vec<char>> = HashMap::new();
        let mut conds: HashMap<char, Vec<char>> = HashMap::new();
        let mut prev: HashMap<char, char> = HashMap::new();
        let mut letters: HashSet<char> = HashSet::new();
        for rel in self.line.iter() {
            letters.insert(rel.0);
            letters.insert(rel.1);
            succs.entry(rel.0).or_default().push(rel.1);
            conds.entry(rel.1).or_default().push(rel.0);
            prev.insert(rel.1, rel.0);
        }
        let mut available: Vec<char> = succs
            .keys()
            .filter(|n| !prev.contains_key(n))
            .copied()
            .collect::<Vec<_>>();
        let mut result: String = String::new();
        let mut workers: [Worker; 5] = [
            Worker::default(),
            Worker::default(),
            Worker::default(),
            Worker::default(),
            Worker::default(),
        ];
        for second in 0.. {
            {
                let workers_jobs = workers.iter().map(|w| w.working).collect::<Vec<_>>();
                for w in workers.iter_mut() {
                    if let Some(job) = w.working {
                        if w.finish_at == second {
                            result.push(job);
                            w.working = None;
                            if let Some(v) = succs.get(&job) {
                                for s in v.iter() {
                                    if !available.contains(s)
                                        && !result.contains(*s)
                                        && workers_jobs.iter().all(|job| *job != Some(*s))
                                    {
                                        available.push(*s);
                                    }
                                }
                            }
                        }
                    }
                }
            }
            if available.is_empty() && workers.iter().all(|w| w.working.is_none()) {
                return second;
            }
            available.sort();
            for w in workers.iter_mut() {
                if w.working.is_some() {
                    continue;
                }
                for (i, cand) in available.iter().enumerate() {
                    if conds
                        .get(cand)
                        .unwrap_or(&vec![])
                        .iter()
                        .all(|c| result.contains(*c))
                    {
                        let c: char = available.remove(i);
                        w.working = Some(c);
                        w.finish_at = second + 60 + (c as u8 - b'A' + 1) as usize;
                        break;
                    }
                }
            }
        }
        0
    }
}
