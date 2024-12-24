//! <https://adventofcode.com/2024/day/24>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{aoc_at, AdventOfCode, ParseError},
        geometric::neighbors,
        parser::parse_usize,
    },
    core::prelude,
    itertools::Itertools,
    rayon::{prelude::*, slice::Windows},
    rustc_data_structures::fx::{FxHashMap, FxHasher},
    serde::Serialize,
    std::{
        cmp::{Ordering, Reverse},
        collections::{BinaryHeap, HashMap, HashSet},
        default,
        hash::BuildHasherDefault,
        ops::Bound,
        panic::resume_unwind,
    },
    winnow::{
        ascii::newline,
        combinator::{alt, repeat, repeat_till, separated, seq, terminated},
        token::one_of,
        PResult, Parser,
    },
};

type Wire = (char, char, char);

fn bit_to_wire(n: usize, prefix: char) -> Wire {
    (
        prefix,
        (b'0' + ((n / 10) as u8)) as char,
        (b'0' + ((n % 10) as u8)) as char,
    )
}

fn wire_to_ord((_, b, c): &(char, char, char)) -> usize {
    (((*b as u8) - b'0') as usize) * 10 + (((*c as u8) - b'0') as usize)
}

fn wire_name((a, b, c): &(char, char, char)) -> String {
    format!("{a}{b}{c}")
}

#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
enum Gate {
    #[default]
    And,
    Or,
    Xor,
}

#[derive(Clone, Debug, Default, Eq, PartialEq, Serialize)]
pub struct Puzzle {
    input_wire: Vec<(Wire, bool)>,
    wire: HashSet<Wire>,
    link: Vec<(Gate, Wire, Wire, Wire)>,
    value: FxHashMap<Wire, bool>,
    wire_downward: HashMap<Wire, HashSet<Wire>>,
    wire_upward: HashMap<Wire, HashSet<Wire>>,
    wire_level: HashMap<Wire, usize>,
    input_bits: usize,
}

impl Puzzle {
    fn seek(
        &self,
        level: usize,
        fixed: HashSet<Wire>,
        swapped: HashSet<Wire>,
    ) -> Option<(Puzzle, HashSet<Wire>)> {
        if level < self.input_bits {
            let relevants = self
                .wire
                .iter()
                .filter(|wire| !fixed.contains(wire))
                .filter(|wire| *self.wire_level.get(wire).unwrap() <= level)
                .collect::<Vec<_>>();
            let mut to_search: Vec<Option<(Wire, Wire)>> = vec![None];
            for (i, pick1) in relevants.iter().enumerate() {
                for pick2 in relevants.iter().skip(i + 1) {
                    to_search.push(Some((**pick1, **pick2)));
                }
            }
            println!("{} :: |set|:{}", level, to_search.len());

            for case in to_search.iter() {
                // println!("{}-{}", wire_name(pick1), wire_name(pick2));
                let checker = if let Some((pick1, pick2)) = case {
                    if 8 < swapped.len() {
                        continue;
                    }
                    self.new_swapped(pick1, pick2)
                } else {
                    self.new()
                };
                let passed = checker.check_exhausitively(level + 1);
                if passed {
                    /* println!(
                        "attemp({:>2}): {:?}: {}",
                        level,
                        case,
                        passed,
                        // aff_x.iter().map(|n| wire_to_ord(n)).collect::<Vec<_>>(),
                        // aff_y.iter().map(|n| wire_to_ord(n)).collect::<Vec<_>>(),
                    ); */
                    let mut f = fixed.clone();
                    for w in self.wire_tree_upward(bit_to_wire(level, 'z')) {
                        f.insert(w);
                    }
                    let mut s = swapped.clone();
                    if let Some((pick1, pick2)) = case {
                        s.insert(*pick1);
                        s.insert(*pick2);
                    }
                    // if let Some(s) = checker.seek(&wrong_bits[1..], f) {
                    //     return Some(s);
                    // }
                    checker.seek(level + 1, f, s);
                }
                // println!(
                //     "  {}{}{}{}: {:?} = {}",
                //     (setting.0 as usize),
                //     (setting.1 as usize),
                //     (setting.2 as usize),
                //     (setting.3 as usize),
                //     v.iter().rev().map(|b| *b as usize).collect::<Vec<_>>(),
                //     val,
                // );
                // let x = (1_usize << level) * (setting.0 as usize);
                // let y = (1_usize << level) * (setting.1 as usize);
                // if x + y != val {
                //     continue 'fail;
                // }
                // println!("{}-{}", wire_name(pick1), wire_name(pick2));

                // let affected1 = self.wire_tree_upward(**pick1);
                // let aff1 = affected1
                //     .iter()
                //     .filter(|n| n.0 == 'x' || n.0 == 'y')
                //     .cloned()
                //     .collect::<HashSet<_>>();
                // let affected2 = self.wire_tree_upward(**pick2);
                // let aff2 = affected2
                //     .iter()
                //     .filter(|n| n.0 == 'x' || n.0 == 'y')
                //     .cloned()
                //     .collect::<HashSet<_>>();
                // let aff = aff1.union(&aff2).cloned().collect::<HashSet<_>>();
                // let aff_x = aff1
                //     .iter()
                //     .filter(|n| n.0 == 'x')
                //     .sorted()
                //     .cloned()
                //     .collect::<Vec<_>>();

                // let aff_y = aff2
                //     .iter()
                //     .filter(|n| n.0 == 'x')
                //     .sorted()
                //     .cloned()
                //     .collect::<Vec<_>>();

                // let checker = self.new_swapped(pick1, pick2);
                // let passed = checker.check_exhausitively(level + 1);
                // if passed {
                //     println!(
                //         "attemp({:>2}): {}-{}: {}, affecting {:?} + {:?}",
                //         level,
                //         wire_name(pick1),
                //         wire_name(pick2),
                //         passed,
                //         aff_x.iter().map(|n| wire_to_ord(n)).collect::<Vec<_>>(),
                //         aff_y.iter().map(|n| wire_to_ord(n)).collect::<Vec<_>>(),
                //     );
                //     let mut f = fixed.clone();
                //     let mut s = swapped.clone();
                //     f.insert(**pick1);
                //     f.insert(**pick2);
                //     // if let Some(s) = checker.seek(&wrong_bits[1..], f) {
                //     //     return Some(s);
                //     // }
                //     checker.seek(level + 1, f, s);
            }
            None
        } else {
            println!(
                "{:?}",
                swapped
                    .iter()
                    .map(|t| format!("{}{}{}", t.0, t.1, t.2))
                    .sorted()
                    .join(",")
            );
            Some((self.clone(), swapped))
        }
    }
    /// return a clean cloned itself
    fn new(&self) -> Puzzle {
        let mut checker = self.clone();
        for (name, b) in checker.value.iter_mut() {
            *b = false;
        }
        checker
    }
    fn new_swapped(&self, pick1: &Wire, pick2: &Wire) -> Puzzle {
        let mut checker = self.new();
        for gate in checker.link.iter_mut() {
            if gate.3 == *pick1 {
                gate.3 = *pick2;
            } else if gate.3 == *pick2 {
                gate.3 = *pick1;
            }
        }
        checker
    }
    fn set_input(&mut self, prefix: char, val: usize) {
        let mut n = val;
        let mut bit_vector: Vec<bool> = Vec::new();
        while 1 < n {
            bit_vector.push(n % 2 == 1);
            n /= 2;
        }
        bit_vector.push(n % 2 == 1);
        for i in 0..self.input_bits {
            let wire = bit_to_wire(i, prefix);
            self.value.insert(wire, bit_vector.get(i) == Some(&true));
        }
    }
    /// exhaustive-check
    fn check_exhausitively(&self, range: usize) -> bool {
        let band = 1_usize << range;
        for target_input1 in 0..=4 {
            let target_value1 = (1_usize << range / 2) + target_input1;
            for target_input2 in 0..=4 {
                let target_value2 = (1_usize << range / 2) + target_input2;
                for offset_x in 0..32 {
                    for offset_y in 0..32 {
                        let mut checker = self.new();
                        let x = target_value1 + offset_x;
                        let y = target_value2 + offset_y;
                        checker.set_input('x', x);
                        checker.set_input('y', y);
                        let (n, v) = checker.eval();
                        if (x + y) % band != n % band {
                            // println!(
                            //     "failed 0..{}: x={}, y={}: {:?}",
                            //     range,
                            //     x,
                            //     y,
                            //     v.iter().rev().map(|b| *b as usize).collect::<Vec<_>>(),
                            // );
                            return false;
                        }
                        if v.len() != self.input_bits + 1 {
                            return false;
                        }
                    }
                }
            }
        }
        true
    }
    /// returns `true` if a now propagaton occured.
    fn evaluate(&mut self, g: Gate, input1: &Wire, input2: &Wire, output: &Wire) -> Option<Wire> {
        let Some(&b1) = self.value.get(input1) else {
            return None;
        };
        let Some(&b2) = self.value.get(input2) else {
            return None;
        };
        let unassigned = self.value.get(output).is_none();
        match g {
            Gate::And => self.value.insert(*output, b1 & b2),
            Gate::Or => self.value.insert(*output, b1 | b2),
            Gate::Xor => self.value.insert(*output, b1 ^ b2),
        };
        unassigned.then(|| *output)
    }
    /// return the evaluation result as a value and a bit vector
    fn eval(&mut self) -> (usize, Vec<bool>) {
        let mut propagated = true;
        let links = self.link.clone();
        while propagated {
            propagated = false;
            for g in links.iter() {
                if self.evaluate(g.0, &g.1, &g.2, &g.3).is_some() {
                    propagated = true;
                }
            }
        }
        let v = self
            .value
            .iter()
            .filter(|(wire, _)| wire.0 == 'z')
            .sorted()
            .map(|(_, b)| b)
            .cloned()
            .collect::<Vec<bool>>();
        let val = v
            .iter()
            .rev()
            .fold(0_usize, |acc, b| acc * 2 + (*b as usize));
        (val, v)
    }
    fn wire_tree_downward(&self, wire: Wire) -> HashSet<Wire> {
        let mut result: HashSet<Wire> = HashSet::new();
        if let Some(downs) = self.wire_downward.get(&wire) {
            let mut to_visit: Vec<Wire> = downs.iter().cloned().collect::<Vec<_>>();
            result.insert(wire);
            while let Some(wire) = to_visit.pop() {
                if result.contains(&wire) {
                    continue;
                }
                result.insert(wire);
                if let Some(subs) = self.wire_downward.get(&wire) {
                    for w in subs.iter() {
                        to_visit.push(*w);
                    }
                } else {
                    assert_eq!(wire.0, 'z');
                }
            }
        } else {
            result.insert(wire);
        }
        result
    }
    fn wire_tree_upward(&self, wire: Wire) -> HashSet<Wire> {
        let mut result: HashSet<Wire> = HashSet::new();
        if let Some(uppers) = self.wire_upward.get(&wire) {
            let mut to_visit: Vec<Wire> = uppers.iter().cloned().collect::<Vec<_>>();
            result.insert(wire);
            while let Some(wire) = to_visit.pop() {
                if result.contains(&wire) {
                    continue;
                }
                result.insert(wire);
                if let Some(subs) = self.wire_upward.get(&wire) {
                    for w in subs.iter() {
                        to_visit.push(*w);
                    }
                } else {
                    assert!(wire.0 == 'x' || wire.0 == 'y');
                }
            }
        } else {
            result.insert(wire);
        }
        result
    }
}

fn parse_wire(s: &mut &str) -> PResult<Wire> {
    (
        one_of('a'..='z'),
        one_of(('a'..='z', '0'..='9')),
        one_of(('a'..='z', '0'..='9')),
    )
        .parse_next(s)
}
fn parse_gate(s: &mut &str) -> PResult<Gate> {
    alt(("AND", "OR", "XOR"))
        .map(|g| match g {
            "AND" => Gate::And,
            "OR" => Gate::Or,
            "XOR" => Gate::Xor,
            _ => unreachable!(),
        })
        .parse_next(s)
}

fn parse_setting(s: &mut &str) -> PResult<(Wire, bool)> {
    seq!(parse_wire, _: ": ", parse_usize)
        .map(|(w, b)| (w, b == 1))
        .parse_next(s)
}

fn parse_connection(s: &mut &str) -> PResult<(Gate, Wire, Wire, Wire)> {
    seq!(parse_wire, _: " ", parse_gate, _: " ", parse_wire, _: " -> ", parse_wire)
        .map(|(in1, g, in2, out)| (g, in1, in2, out))
        .parse_next(s)
}

fn parse(s: &mut &str) -> PResult<(Vec<(Wire, bool)>, Vec<(Gate, Wire, Wire, Wire)>)> {
    seq!(
        separated(1.., parse_setting, newline),
        _: (newline, newline),
        separated(1.., parse_connection, newline)
    )
    .parse_next(s)
}

#[aoc_at(2024, 24)]
impl AdventOfCode for Puzzle {
    type Output1 = usize;
    type Output2 = String;
    fn parse(&mut self, input: String) -> Result<String, ParseError> {
        let (wires, links) = parse(&mut input.as_str())?;
        self.input_wire = wires;
        self.link = links;
        Self::parsed()
    }
    fn end_of_data(&mut self) {
        for (w, b) in self.input_wire.iter() {
            self.value.insert(*w, *b);
            self.wire.insert(*w);
        }
        for (g, i1, i2, o) in self.link.iter() {
            self.wire.insert(*i1);
            self.wire.insert(*i2);
            self.wire.insert(*o);
            self.wire_downward.entry(*i1).or_default().insert(*o);
            self.wire_downward.entry(*i2).or_default().insert(*o);
            self.wire_upward.entry(*o).or_default().insert(*i1);
            self.wire_upward.entry(*o).or_default().insert(*i2);
        }
        self.input_bits = self.input_wire.iter().filter(|(g, _)| g.0 == 'x').count();
    }
    fn serialize(&self) -> Option<String> {
        let mut data = self
            .link
            .iter()
            .enumerate()
            .map(|(i, (g, i1, i2, o))| (wire_name(o), vec![wire_name(i1), wire_name(i2)]))
            .collect::<Vec<_>>();
        for (input, _) in self.input_wire.iter() {
            data.push((wire_name(input), Vec::new()));
        }
        serde_json::to_string(&data).ok()
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut propagated = true;
        let links = self.link.clone();
        while propagated {
            propagated = false;
            for g in links.iter() {
                if self.evaluate(g.0, &g.1, &g.2, &g.3).is_some() {
                    propagated = true;
                }
            }
        }
        self.value
            .iter()
            .filter(|(wire, _)| wire.0 == 'z')
            .sorted()
            .rev()
            .map(|(_, b)| b)
            .fold(0_usize, |acc, b| acc * 2 + (*b as usize))
    }
    #[allow(unreachable_code)]
    fn part2(&mut self) -> Self::Output2 {
        for wire in self.wire.iter() {
            // if wire.0 == 'x' || wire.0 == 'y' {
            //     continue;
            // }

            let inputs = self.wire_tree_upward(*wire);
            let input_range = inputs
                .iter()
                .filter(|n| n.0 == 'x' || n.0 == 'y')
                .map(wire_to_ord)
                .collect::<HashSet<usize>>();
            let input_vec = input_range.iter().cloned().sorted().collect::<Vec<_>>();

            let outputs = self.wire_tree_downward(*wire);
            let output_range = outputs
                .iter()
                .filter(|n| n.0 == 'z')
                .map(wire_to_ord)
                .collect::<HashSet<usize>>();
            let output_vec = output_range.iter().cloned().sorted().collect::<Vec<_>>();

            self.wire_level
                .insert(*wire, *input_range.iter().max().unwrap());
            if *output_range.iter().min().unwrap() < *input_range.iter().max().unwrap() {
                println!(
                    "{}: input from {} to {}, output from {} to {}",
                    wire_name(wire),
                    input_vec[0],
                    input_vec[input_vec.len() - 1],
                    output_vec[0],
                    output_vec[output_vec.len() - 1],
                );
            }
        }
        let mut count: HashMap<usize, usize> = HashMap::new();
        for (w, l) in self.wire_level.iter() {
            *count.entry(*l).or_default() += 1;
        }
        println!("count: {:?}", count.iter().sorted().collect::<Vec<_>>());
        let mut sum_vector: Vec<usize> = vec![0; self.input_bits + 1];
        // let mut res: Vec<String> = Vec::new();
        for target_input1 in 0..self.input_bits {
            let target_value1 = 1_usize << target_input1;
            for target_input2 in (target_input1 + 1)..self.input_bits {
                let target_value2 = 1_usize << target_input2;
                let mut checker = self.new();
                checker.value.insert(bit_to_wire(target_input1, 'x'), true);
                checker.value.insert(bit_to_wire(target_input2, 'y'), true);
                let (n, v) = checker.eval();
                if target_value1 + target_value2 != n {
                    sum_vector[target_input1] += 1;
                    sum_vector[target_input1] += 1;
                    /* println!(
                        "{}, {}: {:?}",
                        target_input1,
                        target_input2,
                        v.iter().rev().map(|b| *b as usize).collect::<Vec<_>>(),
                    ); */
                }
            }
        }
        let wrong_bits = sum_vector
            .iter()
            .enumerate()
            .map(|(i, c)| (*c, i))
            .sorted()
            .rev()
            .map(|(_, i)| i)
            .take(4)
            .collect::<Vec<_>>();
        println!("{sum_vector:?}");
        println!("{wrong_bits:?}");

        if let Some((_, vec)) = self.seek(0, HashSet::new(), HashSet::new()) {
            vec.iter()
                .sorted()
                .map(|t| format!("{}{}{}", t.0, t.1, t.2))
                .join(",")
        } else {
            unreachable!()
        }
    }
}
