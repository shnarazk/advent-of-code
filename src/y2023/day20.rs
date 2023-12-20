//! <https://adventofcode.com/2023/day/20>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::neighbors,
        line_parser, regex,
    },
    itertools::Itertools,
    std::collections::{HashMap, HashSet, VecDeque},
};

#[derive(Debug, Default, Eq, PartialEq)]
pub struct Puzzle {
    modules: HashMap<String, Module>,
    pulses: VecDeque<(String, String, bool)>,
    pulse_counts: (usize, usize),
}

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum ModuleType {
    #[default]
    Broadcast,
    FlipFlop,
    Conjunction,
}
#[derive(Debug, Default, Eq, PartialEq)]
struct Module {
    module_type: ModuleType,
    bool_state: bool,
    hash: HashMap<String, bool>,
    dests: Vec<String>,
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
    fn end_of_data(&mut self) {
        // build hashes
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

        // dbg!(&self.modules);
    }
    fn part1(&mut self) -> Self::Output1 {
        self.start();
        dbg!(self.pulse_counts);
        self.pulse_counts.0 * self.pulse_counts.1
    }
    fn part2(&mut self) -> Self::Output2 {
        2
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
}
