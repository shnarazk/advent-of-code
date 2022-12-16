//! <https://adventofcode.com/2022/day/16>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::neighbors,
        line_parser, regex,
    },
    std::{
        cmp::Reverse,
        collections::{BinaryHeap, HashMap, HashSet},
    },
};

#[derive(Debug, Default, Eq, PartialEq)]
pub struct Puzzle {
    line: Vec<(String, usize, Vec<String>)>,
    map: HashMap<String, (usize, Vec<String>)>,
    distance: HashMap<(String, String), usize>,
}

#[aoc(2022, 16)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    // fn header(&mut self, input: String) -> Result<String, ParseError> {
    //     let parser = regex!(r"^(.+)\n\n((.|\n)+)$");
    //     let segment = parser.captures(input).ok_or(ParseError)?;
    //     for num in segment[1].split(',') {
    //         let _value = num.parse::<usize>()?;
    //     }
    //     Ok(segment[2].to_string())
    // }
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        let parser =
            regex!(r"^Valve (\w+) has flow rate=(\d+); tunnels? leads? to valves? ((\w+, )*\w+)$");
        let segment = parser.captures(block).ok_or(ParseError)?;
        self.line.push((
            segment[1].to_string(),
            segment[2].parse::<usize>()?,
            segment[3]
                .split(", ")
                .map(|s| s.to_string())
                .collect::<Vec<_>>(),
        ));
        Ok(())
    }
    fn after_insert(&mut self) {
        for (label, flow, linked) in self.line.iter() {
            self.map.insert(label.clone(), (*flow, linked.clone()));
        }
        self.initialize_distacnes();
        dbg!(&self.distance.len());
        dbg!(&self.distance.get(&("BB".to_string(), "JJ".to_string())));
    }
    fn part1(&mut self) -> Self::Output1 {
        let init = State {
            path: vec!["AA".to_string()],
            time: 0,
            contribution: vec![(0, 0)],
            ..Default::default()
        };
        self.traverse(init)
    }
    fn part2(&mut self) -> Self::Output2 {
        0
    }
}

#[derive(Debug, Default, Eq, PartialEq)]
struct State {
    path: Vec<String>,
    time: usize,
    flow: usize,
    contribution: Vec<(usize, usize)>,
}

impl Puzzle {
    fn initialize_distacnes(&mut self) {
        let labels = self.map.keys().cloned().collect::<Vec<_>>();
        for l in labels.iter() {
            self.initialize_distances_from(l.to_string());
        }
    }
    fn initialize_distances_from(&mut self, label: String) {
        #[derive(Debug, Eq, Ord, PartialEq, PartialOrd)]
        struct State<'a> {
            time: usize,
            loc: &'a String,
        }
        self.distance.insert((label.clone(), label.clone()), 0);
        let mut to_visit = BinaryHeap::new();
        to_visit.push(Reverse(State {
            loc: &label,
            time: 0,
        }));
        let mut visited: HashSet<&String> = HashSet::new();
        visited.insert(&label);
        while let Some(Reverse(state)) = to_visit.pop() {
            for next in self.map.get(state.loc).unwrap().1.iter() {
                let key = (label.clone(), next.clone());
                if let std::collections::hash_map::Entry::Vacant(e) = self.distance.entry(key) {
                    e.insert(state.time + 1);
                    to_visit.push(Reverse(State {
                        loc: next,
                        time: state.time + 1,
                    }));
                }
            }
        }
    }
    fn traverse(&self, state: State) -> usize {
        if state.time == 30 {
            return state.flow;
        }
        let mut best = state.flow;
        let now = state.path.last().unwrap();
        for ((_, next), dist) in self.distance.iter().filter(|((s, g), d)| s == now) {
            if state.path.contains(next) {
                continue;
            }
            let time = state.time + *dist + 1;
            if 30 <= time {
                continue;
            }
            let f = self.map.get(next).unwrap().0;
            if f == 0 {
                continue;
            }
            let value = (30 - time) * f;
            let mut contribution = state.contribution.clone();
            contribution.push((time, self.map.get(next).unwrap().0));
            let mut path = state.path.clone();
            path.push(next.clone());
            best = self
                .traverse(State {
                    path,
                    time,
                    flow: state.flow + value,
                    contribution,
                })
                .max(best);
        }
        best
    }
}
