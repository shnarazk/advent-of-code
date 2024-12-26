//! <https://adventofcode.com/2024/day/24>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
#![allow(clippy::type_complexity)]
use {
    crate::{
        framework::{aoc_at, AdventOfCode, ParseError},
        parser::parse_usize,
        progress,
    },
    itertools::Itertools,
    // rayon::{prelude::*, slice::Windows},
    rustc_data_structures::fx::{FxHashMap, FxHasher},
    serde::Serialize,
    std::{
        collections::{HashMap, HashSet},
        hash::BuildHasherDefault,
        sync::OnceLock,
    },
    winnow::{
        ascii::newline,
        combinator::{alt, separated, seq},
        token::one_of,
        PResult, Parser,
    },
};

/// convert a `usize` to its binary representation
fn int_to_bit_vector(mut n: usize, l: usize) -> Vec<bool> {
    let mut bit_vector: Vec<bool> = Vec::new();
    while 1 < n {
        bit_vector.push(n % 2 == 1);
        n /= 2;
    }
    bit_vector.push(n % 2 == 1);
    while bit_vector.len() < l {
        bit_vector.push(false);
    }
    bit_vector
}

#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
enum Gate {
    #[default]
    And,
    Or,
    Xor,
}

type Wire = (char, char, char);

type GateSpec = (Gate, Wire, Wire, Wire);

/// convert from 'ord', 0 to 43, to wire
fn bit_to_wire(n: usize, prefix: char) -> Wire {
    (
        prefix,
        (b'0' + ((n / 10) as u8)) as char,
        (b'0' + ((n % 10) as u8)) as char,
    )
}

/// convert a `Wire` type to its 'ord', 0 to 43
fn wire_to_ord((_, b, c): &Wire) -> usize {
    (((*b as u8) - b'0') as usize) * 10 + (((*c as u8) - b'0') as usize)
}

/// convert  `Wire` to its string representation
fn wire_name((a, b, c): &Wire) -> String {
    format!("{a}{b}{c}")
}

#[derive(Clone, Debug, Default, Eq, PartialEq, Serialize)]
pub struct Adder {
    overrides: Vec<GateSpec>,
}

impl Adder {
    fn new(pairs: Vec<(GateSpec, GateSpec)>) -> Adder {
        let overrides = pairs
            .iter()
            .flat_map(|(g1, g2)| [*g1, *g2])
            .collect::<Vec<_>>();
        Adder { overrides }
    }
    fn evaluate(
        &self,
        values: &mut FxHashMap<Wire, bool>,
        (g, arg1, arg2, output): &(Gate, Wire, Wire, Wire),
    ) -> Option<Wire> {
        let b1 = *values.get(arg1)?;
        let b2 = *values.get(arg2)?;
        let unassigned = values.get(output).is_none();
        match g {
            Gate::And => values.insert(*output, b1 & b2),
            Gate::Or => values.insert(*output, b1 | b2),
            Gate::Xor => values.insert(*output, b1 ^ b2),
        };
        unassigned.then_some(*output)
    }
    fn add(&self, arg1: usize, arg2: usize) -> (usize, Vec<bool>) {
        let input_bits = *INPUT_BITS.get().unwrap();
        let bit1 = int_to_bit_vector(arg1, input_bits);
        let bit2 = int_to_bit_vector(arg2, input_bits);

        let mut values: FxHashMap<Wire, bool> =
            HashMap::<_, _, BuildHasherDefault<FxHasher>>::default();

        for i in 0..input_bits {
            let wire = bit_to_wire(i, 'x');
            values.insert(wire, bit1.get(i) == Some(&true));
        }
        for i in 0..input_bits {
            let wire = bit_to_wire(i, 'y');
            values.insert(wire, bit2.get(i) == Some(&true));
        }

        let mut propagated = true;
        let base_config = BASE_LINK.get().unwrap();
        while propagated {
            propagated = false;
            for gate in self.overrides.iter() {
                if self.evaluate(&mut values, gate).is_some() {
                    propagated = true;
                    continue;
                }
            }
            for gate in base_config.iter() {
                if self.evaluate(&mut values, gate).is_some() {
                    propagated = true;
                }
            }
        }
        let v = values
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
    fn wrong_bit(&self) -> Option<usize> {
        let input_bits = *INPUT_BITS.get().unwrap();
        let mut target: Option<usize> = None;
        for bit1 in 0..=input_bits {
            let target_value1 = 1_usize << bit1;
            for bit2 in (bit1 + 1)..=input_bits {
                let target_value2 = 1_usize << bit2;
                for offset_x in 0..2 {
                    for offset_y in 0..2 {
                        let x = target_value1 + offset_x;
                        let y = target_value2 + offset_y;

                        let (n, v) = self.add(x, y);
                        let ans_bit = int_to_bit_vector(x + y, input_bits + 1);
                        for (i, b) in v.iter().enumerate() {
                            if *b != *ans_bit.get(i).unwrap_or(&false) {
                                target = target.map_or(Some(i), |b| Some(b.min(i)));
                            }
                        }
                        if v.len() != input_bits + 1 {
                            let l = v.len() + 1;
                            target = target.map_or(Some(l), |b| Some(b.min(l)));
                            // println!(
                            //     "failed 0..{}: x={}, y={}: {:?}",
                            //     range,
                            //     x,
                            //     y,
                            //     v.iter().rev().map(|b| *b as usize).collect::<Vec<_>>(),
                            // );
                        }
                    }
                }
            }
        }
        target
    }
    /// return `(down_tree, up_tree)`
    fn wire_affects(&self, wire: Wire) -> (HashSet<Wire>, HashSet<Wire>) {
        let base_links = BASE_LINK.get().unwrap();
        let mut wires: HashSet<Wire> = HashSet::new();
        let mut down_tree: HashMap<Wire, HashSet<Wire>> = HashMap::new();
        let mut up_tree: HashMap<Wire, HashSet<Wire>> = HashMap::new();
        for entry in base_links.iter() {
            let (g, i1, i2, o) = self.overrides.iter().find(|_| true).map_or(entry, |e| e);
            wires.insert(*i1);
            wires.insert(*i2);
            wires.insert(*o);
            down_tree.entry(*i1).or_default().insert(*o);
            down_tree.entry(*i2).or_default().insert(*o);
            up_tree.entry(*o).or_default().insert(*i1);
            up_tree.entry(*o).or_default().insert(*i2);
        }
        let mut down_subtree: HashSet<Wire> = HashSet::new();
        if let Some(downs) = down_tree.get(&wire) {
            let mut to_visit: Vec<Wire> = downs.iter().cloned().collect::<Vec<_>>();
            down_subtree.insert(wire);
            while let Some(wire) = to_visit.pop() {
                if down_subtree.contains(&wire) {
                    continue;
                }
                down_subtree.insert(wire);
                if let Some(subs) = down_tree.get(&wire) {
                    for w in subs.iter() {
                        to_visit.push(*w);
                    }
                } else {
                    assert_eq!(wire.0, 'z');
                }
            }
        }
        let mut up_subtree: HashSet<Wire> = HashSet::new();
        if let Some(uppers) = up_tree.get(&wire) {
            let mut to_visit: Vec<Wire> = uppers.iter().cloned().collect::<Vec<_>>();
            up_subtree.insert(wire);
            while let Some(wire) = to_visit.pop() {
                if up_subtree.contains(&wire) {
                    continue;
                }
                up_subtree.insert(wire);
                if let Some(subs) = up_tree.get(&wire) {
                    for w in subs.iter() {
                        to_visit.push(*w);
                    }
                } else {
                    assert!(wire.0 == 'x' || wire.0 == 'y');
                }
            }
        } else {
            up_subtree.insert(wire);
        }
        (down_subtree, up_subtree)
    }
}

fn wrong_bit(memo: &mut HashMap<Vec<Wire>, Option<usize>>, swaps: Vec<Wire>) -> Option<usize> {
    unimplemented!()
}

static BASE_LINK: OnceLock<Vec<(Gate, Wire, Wire, Wire)>> = OnceLock::new();
static INPUT_BITS: OnceLock<usize> = OnceLock::new();

fn build_swapped_pair((pick1, pick2): &(Wire, Wire)) -> (GateSpec, GateSpec) {
    let (p1, p2) = if pick1 < pick2 {
        (pick1, pick2)
    } else {
        (pick2, pick1)
    };
    let specs = BASE_LINK.get().unwrap();
    let spec1: &GateSpec = specs.iter().find(|(_, _, _, o)| *o == *pick1).unwrap();
    let spec2: &GateSpec = specs.iter().find(|(_, _, _, o)| *o == *pick2).unwrap();
    (
        (spec1.0, spec1.1, spec1.2, *pick2),
        (spec2.0, spec2.1, spec2.2, *pick1),
    )
}

#[derive(Clone, Debug, Default, Eq, PartialEq, Serialize)]
pub struct Puzzle {
    input_wire: Vec<(Wire, bool)>,
    wire: HashSet<Wire>,
    wire_level: HashMap<Wire, usize>,
}

impl Puzzle {
    fn seek(
        &self,
        level: usize,
        // fixed: HashSet<Wire>,
        swapped: Vec<(Wire, Wire)>,
        memo: &mut HashMap<(usize, Vec<(Wire, Wire)>), bool>,
    ) -> Option<Vec<(Wire, Wire)>> {
        let input_bits = *INPUT_BITS.get().unwrap();
        if let Some(b) = memo.get(&(level, swapped.clone())) {
            return if *b { Some(swapped) } else { None };
        }
        if level == input_bits {
            /*
            if swapped.len() == 8 && self.final_check(self.input_bits) {
                println!(
                    "{:?}",
                    swapped
                        .iter()
                        .map(|(f, t)| format!("{}{}{}", t.0, t.1, t.2))
                        .sorted()
                        .join(",")
                );
                memo.insert((level, swapped.clone()), true);
                return Some(swapped);
            } else {
                memo.insert((level, swapped.clone()), false);
                return None;
            }
            */
            return None;
        }

        let relevants = self
            .wire
            .iter()
            .filter(|wire| wire.0 != 'x' && wire.0 != 'y')
            .filter(|wire| !swapped.iter().any(|(w1, w2)| w1 == *wire || w2 == *wire))
            // .filter(|wire| *self.wire_level.get(wire).unwrap() <= level + 1)
            .sorted()
            .collect::<Vec<_>>();
        let mut to_search: Vec<(Wire, Wire)> = vec![];
        let mut num_lifts: usize = 0;
        let adder = Adder::new(vec![]);
        for (i, pick1) in relevants.iter().enumerate() {
            let pick1_level = adder
                .wire_affects(**pick1)
                .0
                .contains(&bit_to_wire(level, 'z'));
            for pick2 in relevants.iter().skip(i + 1) {
                let pick2_level = adder
                    .wire_affects(**pick2)
                    .0
                    .contains(&bit_to_wire(level, 'z'));
                if pick1_level || pick2_level {
                    to_search.push((**pick1, **pick2));
                }
            }
        }
        let search_space = to_search.len();
        for (i, case) in to_search.iter().enumerate() {
            // println!("{}-{}", wire_name(pick1), wire_name(pick2));
            if 8 < swapped.len() {
                continue;
            }
            progress!(format!(
                "{:>10} level:{level:>2}({i:>5}/{search_space:>5}) lift:{num_lifts:>5}:: {}-{}",
                memo.len(),
                wire_name(&case.0),
                wire_name(&case.1)
            ));
            let mut swapps: Vec<(GateSpec, GateSpec)> =
                swapped.iter().map(build_swapped_pair).collect::<Vec<_>>();
            swapps.push(build_swapped_pair(case));
            let checker = Adder::new(swapps);

            if let Some(bit) = checker.wrong_bit() {
                /* println!(
                    "attemp({:>2}): {:?}: {}",
                    level,
                    case,
                    passed,
                    // aff_x.iter().map(|n| wire_to_ord(n)).collect::<Vec<_>>(),
                    // aff_y.iter().map(|n| wire_to_ord(n)).collect::<Vec<_>>(),
                ); */
                if bit <= level {
                    continue;
                }
                let mut s = swapped.clone();
                s.push(*case);
                s.sort_unstable();
                num_lifts += 1;
                if let Some(ret) = self.seek(bit, s, memo) {
                    if ret.len() == 8 {
                        memo.insert((level, swapped), true);
                        return Some(ret);
                    } else {
                        // memo.insert((level, swapped.clone()), false);
                    }
                } else {
                    memo.insert((level, swapped.clone()), false);
                }
            } else {
                assert!(checker.wrong_bit().is_none());
                println!("{swapped:?}");
                return Some(swapped);
            }
        }
        memo.insert((level, swapped.clone()), false);
        None
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

fn parse_connection(s: &mut &str) -> PResult<GateSpec> {
    seq!(parse_wire, _: " ", parse_gate, _: " ", parse_wire, _: " -> ", parse_wire)
        .map(|(in1, g, in2, out)| (g, in1, in2, out))
        .parse_next(s)
}

fn parse(s: &mut &str) -> PResult<(Vec<(Wire, bool)>, Vec<GateSpec>)> {
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
        for (g, i1, i2, o) in links.iter() {
            self.wire.insert(*i1);
            self.wire.insert(*i2);
            self.wire.insert(*o);
        }
        if BASE_LINK.get().is_none() {
            BASE_LINK.set(links).unwrap();
        }
        Self::parsed()
    }
    fn end_of_data(&mut self) {
        for (w, b) in self.input_wire.iter() {
            self.wire.insert(*w);
        }
        let input_bits = self.input_wire.iter().filter(|(g, _)| g.0 == 'x').count();
        if INPUT_BITS.get().is_none() {
            INPUT_BITS.set(input_bits).unwrap();
        }
    }
    fn serialize(&self) -> Option<String> {
        let links = BASE_LINK.get().unwrap();
        let mut data = links
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
        let x = self
            .input_wire
            .iter()
            .filter(|(wire, _)| wire.0 == 'x')
            .sorted()
            .rev()
            .map(|(_, b)| b)
            .fold(0_usize, |acc, b| acc * 2 + (*b as usize));
        let y = self
            .input_wire
            .iter()
            .filter(|(wire, _)| wire.0 == 'y')
            .sorted()
            .rev()
            .map(|(_, b)| b)
            .fold(0_usize, |acc, b| acc * 2 + (*b as usize));

        Adder::new(Vec::new()).add(x, y).0
    }
    #[allow(unreachable_code)]
    fn part2(&mut self) -> Self::Output2 {
        /*
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
                .insert(*wire, *output_range.iter().min().unwrap());
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

        let mut memo: HashMap<(usize, Vec<Wire>), bool> = HashMap::new();
        if let Some(vec) = self.seek(0, Vec::new(), &mut memo) {
            vec.iter()
                .sorted()
                .map(|t| format!("{}{}{}", t.0, t.1, t.2))
                .join(",")
        } else {
            unreachable!()
        }
        */
        "".to_string()
    }
}
