//! <https://adventofcode.com/2024/day/24>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{aoc_at, AdventOfCode, ParseError},
        geometric::neighbors,
        parser::parse_usize,
        progress,
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
        sync::OnceLock,
    },
    winnow::{
        ascii::newline,
        combinator::{alt, repeat, repeat_till, separated, seq, terminated},
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
        let Some(&b1) = values.get(arg1) else {
            return None;
        };
        let Some(&b2) = values.get(arg2) else {
            return None;
        };
        let unassigned = values.get(output).is_none();
        match g {
            Gate::And => values.insert(*output, b1 & b2),
            Gate::Or => values.insert(*output, b1 | b2),
            Gate::Xor => values.insert(*output, b1 ^ b2),
        };
        unassigned.then(|| *output)
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
                if self.evaluate(&mut values, &gate).is_some() {
                    propagated = true;
                    continue;
                }
            }
            for gate in base_config.iter() {
                if self.evaluate(&mut values, &gate).is_some() {
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
    link: Vec<(Gate, Wire, Wire, Wire)>,
    value: FxHashMap<Wire, bool>,
    wire_downward: HashMap<Wire, HashSet<Wire>>,
    wire_upward: HashMap<Wire, HashSet<Wire>>,
    /// most least bit affected by wire
    wire_level: HashMap<Wire, usize>,
    input_bits: usize,
}

impl Puzzle {
    fn seek(
        &self,
        level: usize,
        // fixed: HashSet<Wire>,
        swapped: Vec<(Wire, Wire)>,
        memo: &mut HashMap<(usize, Vec<(Wire, Wire)>), bool>,
    ) -> Option<Vec<(Wire, Wire)>> {
        if let Some(b) = memo.get(&(level, swapped.clone())) {
            return if *b { Some(swapped) } else { None };
        }
        if level == self.input_bits {
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
            .filter(|wire| {
                !swapped
                    .iter()
                    .find(|(w1, w2)| w1 == *wire || w2 == *wire)
                    .is_some()
            })
            // .filter(|wire| *self.wire_level.get(wire).unwrap() <= level + 1)
            .sorted()
            .collect::<Vec<_>>();
        let mut to_search: Vec<(Wire, Wire)> = vec![];
        let mut num_lifts: usize = 0;
        for (i, pick1) in relevants.iter().enumerate() {
            let pick1_level = self
                .wire_tree_downward(**pick1)
                .contains(&bit_to_wire(level, 'z'));
            for pick2 in relevants.iter().skip(i + 1) {
                let pick2_level = self
                    .wire_tree_downward(**pick2)
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
            swapps.push(build_swapped_pair(&case));
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
    /*
    /// return a clean cloned itself
    fn new(&self) -> Puzzle {
        let mut checker = self.clone();
        for (name, b) in checker.value.iter_mut() {
            *b = false;
        }
        checker
    }
    */
    /*
    fn new_swapped(&self, pick1: &Wire, pick2: &Wire) -> Puzzle {
        let mut checker = self.new();
        for gate in checker.link.iter_mut() {
            if gate.3 == *pick1 {
                gate.3 = *pick2;
            } else if gate.3 == *pick2 {
                gate.3 = *pick1;
            }
        }
        checker.wire.clear();
        checker.wire_downward.clear();
        checker.wire_upward.clear();
        for (g, i1, i2, o) in checker.link.iter() {
            checker.wire.insert(*i1);
            checker.wire.insert(*i2);
            checker.wire.insert(*o);
            checker.wire_downward.entry(*i1).or_default().insert(*o);
            checker.wire_downward.entry(*i2).or_default().insert(*o);
            checker.wire_upward.entry(*o).or_default().insert(*i1);
            checker.wire_upward.entry(*o).or_default().insert(*i2);
        }
        checker
    }
    */
    /*
    fn set_input(&mut self, prefix: char, val: usize) {
        let bit_vector: Vec<bool> = int_to_bit_vector(val);
        for i in 0..self.input_bits {
            let wire = bit_to_wire(i, prefix);
            self.value.insert(wire, bit_vector.get(i) == Some(&true));
        }
    }
    */
    /*
    /// exhaustive-check
    fn check_exhausitively(&self, range: usize) -> bool {
        let band = 2_usize << range;
        for target_input1 in 0..=4 {
            let target_value1 = (1_usize << range) + target_input1;
            for target_input2 in 0..=4 {
                let target_value2 = (1_usize << range) + target_input2;
                for offset_x in 0..4 {
                    for offset_y in 0..4 {
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
    */
    /*
    /// exhaustive-check
    fn final_check(&self, from: usize) -> bool {
        let band = (1_usize << from) / 2;
        for target_input1 in 0..self.input_bits {
            let target_value1 = 1_usize << target_input1;
            for target_input2 in (target_input1 + 1)..self.input_bits {
                let target_value2 = 1_usize << target_input2;
                for offset_x in 0..4 {
                    for offset_y in 0..4 {
                        let mut checker = self.new();
                        let x = target_value1 + offset_x;
                        let y = target_value2 + offset_y;
                        checker.set_input('x', x);
                        checker.set_input('y', y);
                        let (n, v) = checker.eval();
                        println!(
                            "failed 0..{}: {}+{}={}: {:?}",
                            from,
                            x,
                            y,
                            x + y,
                            v.iter().rev().map(|b| *b as usize).collect::<Vec<_>>(),
                        );
                        if (x + y) / band != n / band {
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
    */
    /*
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
    */
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
        let input_bits = self.input_wire.iter().filter(|(g, _)| g.0 == 'x').count();
        if INPUT_BITS.get().is_none() {
            INPUT_BITS.set(input_bits).unwrap();
        }
        if BASE_LINK.get().is_none() {
            BASE_LINK.set(self.link.clone()).unwrap();
        }
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
