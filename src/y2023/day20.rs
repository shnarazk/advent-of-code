//! <https://adventofcode.com/2023/day/20>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::neighbors,
        line_parser,
        math::crt,
        regex,
    },
    itertools::Itertools,
    std::collections::{HashMap, HashSet, VecDeque},
};

#[derive(Debug, Default, Eq, PartialEq)]
pub struct Puzzle {
    modules: HashMap<String, Module>,
    pulses: VecDeque<(String, String, bool)>,
    pulse_counts: (usize, usize),
    // low-pulse modulo and high-pulse modulo
    chinese: Option<((usize, usize), (usize, usize))>,
}

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum ModuleType {
    #[default]
    Broadcast,
    FlipFlop,
    Conjunction,
}

#[derive(Debug, Default, Eq, PartialEq)]
struct Node {
    depth: usize,
    hash: Vec<usize>,
    dests: Vec<usize>,
}

impl Node {
    fn output(&self, n: usize) -> Option<bool> {
        (n % 2_usize.pow((self.depth - 1) as u32) == 0)
            .then_some(n % 2usize.pow(self.depth as u32) == 0)
    }
}

#[derive(Debug, Default, Eq, PartialEq)]
struct Module {
    chinese: Option<(usize, usize)>,
    module_type: ModuleType,
    bool_state: bool,
    hash: HashMap<String, bool>,
    dests: Vec<String>,
    sources: Vec<String>,
    bits: Vec<bool>,
}

impl<'a> Module {
    fn receive_pulse(&'a mut self, from: &'a String, high_pulse: bool) -> Option<bool> {
        match self.module_type {
            ModuleType::Broadcast => Some(high_pulse),
            ModuleType::FlipFlop => (!high_pulse).then(|| {
                self.bool_state = !self.bool_state;
                self.bool_state
            }),
            ModuleType::Conjunction => {
                self.hash.insert(from.to_string(), high_pulse);
                Some(!self.hash.values().all(|b| *b))
            }
        }
    }
}

#[aoc(2023, 20)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        let segment = block.split(" -> ").collect::<Vec<_>>();
        let mut label = segment[0].chars();
        let (module_type, module_name) = match label.next().unwrap() {
            '%' => (ModuleType::FlipFlop, label.collect::<String>()),
            '&' => (ModuleType::Conjunction, label.collect::<String>()),
            'b' if segment[0] == "broadcaster" => (ModuleType::Broadcast, segment[0].to_string()),
            _ => unreachable!(),
        };
        let dests = segment[1]
            .split(", ")
            .map(|s| s.to_string())
            .collect::<Vec<_>>();
        let module = Module {
            module_type,
            dests,
            ..Module::default()
        };
        self.modules.insert(module_name, module);
        Ok(())
    }
    fn end_of_data(&mut self) {}
    fn part1(&mut self) -> Self::Output1 {
        // self.start();
        self.pulse_counts.0 * self.pulse_counts.1
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut map: HashMap<String, Vec<String>> = HashMap::new();
        for (from, m) in self.modules.iter() {
            for to in m.dests.iter() {
                let entry = map.entry(to.clone()).or_insert(Vec::new());
                entry.push(from.to_string());
            }
        }
        for (name, m) in self.modules.iter_mut() {
            if let Some(inputs) = map.get(name) {
                m.hash = inputs
                    .iter()
                    .map(|n| (n.to_string(), false))
                    .collect::<HashMap<String, bool>>();
            }
        }
        let mut subset: HashSet<String> = HashSet::new();
        let mut to_visit: Vec<&str> = vec!["dh"];
        while let Some(n) = to_visit.pop() {
            if subset.contains(n) {
                continue;
            }
            subset.insert(n.to_string());
            if let Some(inputs) = map.get(n) {
                for input in inputs.iter() {
                    to_visit.push(input);
                }
            }
        }
        dbg!(self.modules.len());
        dbg!(subset.len());
        let n1 = Node {
            depth: 1,
            ..Node::default()
        };
        let n2 = Node {
            depth: 2,
            ..Node::default()
        };
        let n3 = Node {
            depth: 3,
            ..Node::default()
        };
        for n in 0..8 {
            println!("{}: {:?}", n, n1.output(n));
        }
        for n in 0..8 {
            println!("{}: {:?}", n, n2.output(n));
        }
        for n in 0..8 {
            println!("{}: {:?}", n, n3.output(n));
        }
        self.pulses_to_activete()
    }
}

impl Puzzle {
    fn start(&mut self) {
        let mut _history = HashSet::from([self.dump()]);
        for _ in 0..1000 {
            self.pulses
                .push_back(("".to_string(), "broadcaster".to_string(), false));
            self.pulse_counts.0 += 1;
            self.dispatch();
        }
    }
    fn pulses_to_activete(&mut self) -> usize {
        let mut _history = HashSet::from([self.dump()]);
        self.propagate();
        dbg!();
        if self.chinese.is_some() {
            dbg!(&self.chinese);
            return 1;
        }
        unreachable!()
    }
    fn dispatch(&mut self) {
        while let Some((from, to, pulse)) = self.pulses.pop_front() {
            let Some(target) = self.modules.get_mut(&to) else {
                continue;
            };
            if let Some(output) = target.receive_pulse(&from, pulse) {
                target
                    .dests
                    .iter()
                    .for_each(|d| self.pulses.push_back((to.clone(), d.clone(), output)));
                if output {
                    self.pulse_counts.1 += target.dests.len();
                } else {
                    self.pulse_counts.0 += target.dests.len();
                }
            }
        }
    }
    fn dump(&self) -> Vec<(bool, Vec<(&String, &bool)>)> {
        self.modules
            .iter()
            .map(|(name, m)| {
                (
                    name,
                    (m.bool_state, m.hash.iter().sorted().collect::<Vec<_>>()),
                )
            })
            .sorted()
            .map(|(_, m)| m)
            .collect::<Vec<_>>()
    }
    fn propagate(&mut self) {
        self.pulses
            .push_back(("".to_string(), "broadcaster".to_string(), false));
        while let Some((from, to, pulse)) = self.pulses.pop_front() {
            dbg!(&to);
            let Some(target) = self.modules.get(&to) else {
                continue;
            };
            if target.chinese.is_some() {
                continue;
            }
            let mut chinese: Option<(usize, usize)> = None;
            match target.module_type {
                ModuleType::Broadcast => chinese = Some((2, 0)),
                ModuleType::FlipFlop => {
                    if let Some(f) = self.modules.get(&from) {
                        chinese = f.chinese.map(|(p, q)| (2 * p, 2 * q));
                    }
                }
                ModuleType::Conjunction
                    if target
                        .hash
                        .keys()
                        .all(|name| self.modules.get(name).unwrap().chinese.is_some()) =>
                {
                    let seeds = target
                        .hash
                        .keys()
                        .map(|name| self.modules.get(name).unwrap().chinese.unwrap())
                        .collect::<Vec<_>>();
                    chinese = seeds.iter().copied().reduce(|p, q| crt(p, q));
                }
                _ => (),
            }
            let target = self.modules.get_mut(&to).unwrap();
            if chinese.is_some() {
                target
                    .dests
                    .iter()
                    .for_each(|d| self.pulses.push_back((to.clone(), d.clone(), false)));
                target.chinese = chinese;
                if chinese.is_some() && target.dests.contains(&"rx".to_string()) {
                    self.chinese = chinese;
                }
            } else {
                self.pulses.push_back((to.clone(), from.clone(), false));
            }
        }
    }
}
