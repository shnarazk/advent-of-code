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
    rayon::{prelude::*, slice::Windows},
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

fn fmt(v: &[bool]) -> String {
    format!(
        "{}|{}|0({})",
        v.len(),
        v.iter()
            .rev()
            .map(|b| if *b { 'x' } else { '.' })
            .collect::<String>(),
        v.iter().filter(|b| **b).count(),
    )
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
    fn wrong_bit(&self) -> usize {
        let input_bits = *INPUT_BITS.get().unwrap();
        (0..=input_bits - 1)
            .collect::<Vec<_>>()
            .par_iter()
            .map(|bit1| {
                let target_value1 = 1_usize << bit1;
                ((bit1 + 1)..=input_bits)
                    .map(|bit2| {
                        let x = target_value1;
                        let y = 1_usize << bit2;
                        let (n, v) = self.add(x, y);
                        let ans_bit = int_to_bit_vector(x + y, input_bits + 1);
                        let mut target: Option<usize> = None;
                        for (i, b) in v.iter().enumerate() {
                            if *b != *ans_bit.get(i).unwrap_or(&false) {
                                target = target.map_or(Some(i), |b| Some(b.min(i)));
                                break;
                            }
                        }
                        if v.len() != input_bits + 1 {
                            let l = v.len() + 1;
                            target = target.map_or(Some(l), |b| Some(b.min(l)));
                        }
                        target.map_or(input_bits + 1, |n| n)
                    })
                    .min()
                    .unwrap()
            })
            .min()
            .unwrap()
    }
    fn wrong_bits(&self) -> Vec<bool> {
        let input_bits = *INPUT_BITS.get().unwrap();
        let ret = (0..=input_bits)
            .collect::<Vec<_>>()
            .par_iter()
            .map(|bit1| {
                let target_value1 = 1_usize << (*bit1).min(input_bits - 1);
                (0..input_bits)
                    .map(|bit2| {
                        let x = target_value1;
                        let y = 1_usize << bit2;
                        let ans_bit = int_to_bit_vector(x + y, input_bits + 1);
                        let (_, v) = self.add(x, y);

                        v.get(*bit1).map_or(true, |b| *b != ans_bit[*bit1])
                    })
                    .any(|b| b)
            })
            .collect::<Vec<_>>();
        ret.iter()
            .fold((Vec::new(), false), |(mut acc, pre), b| match (pre, *b) {
                (false, b) => {
                    acc.push(b);
                    (acc, b)
                }
                (true, false) => {
                    acc.push(false);
                    (acc, false)
                }
                (true, true) => {
                    acc.push(false);
                    (acc, true)
                }
            })
            .0
    }
    fn affect_bits(&self, origin: &Adder) -> Vec<bool> {
        let input_bits = *INPUT_BITS.get().unwrap();
        let ret = (0..=input_bits)
            .collect::<Vec<_>>()
            .par_iter()
            .map(|bit1| {
                let target_value1 = 1_usize << (*bit1).min(input_bits - 1);
                (0..input_bits)
                    .map(|bit2| {
                        let target_value2 = 1_usize << bit2;
                        [[0, 0], [0, 1], [1, 0], [0, 0]]
                            .iter()
                            .fold(false, |acc, pattern| {
                                let x = target_value1 * pattern[0];
                                let y = target_value2 * pattern[1];
                                let base = origin.add(x, y).1;
                                let v = self.add(x, y).1;
                                acc || v.get(*bit1).map_or(true, |b| *b != base[*bit1])
                            })
                    })
                    .any(|b| b)
            })
            .collect::<Vec<_>>();
        ret.iter()
            .fold((Vec::new(), false), |(mut acc, pre), b| match (pre, *b) {
                (false, b) => {
                    acc.push(b);
                    (acc, b)
                }
                (true, false) => {
                    acc.push(false);
                    (acc, false)
                }
                (true, true) => {
                    acc.push(false);
                    (acc, true)
                }
            })
            .0
    }
    /// return `(down_tree, up_tree)`
    fn wire_trees(&self) -> (HashMap<Wire, HashSet<Wire>>, HashMap<Wire, HashSet<Wire>>) {
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
        (down_tree, up_tree)
    }
    fn wire_affects(&self, tree: &HashMap<Wire, HashSet<Wire>>, wire: Wire) -> HashSet<Wire> {
        let mut subtree: HashSet<Wire> = HashSet::new();
        if let Some(linked) = tree.get(&wire) {
            let mut to_visit: Vec<Wire> = linked.iter().cloned().collect::<Vec<_>>();
            subtree.insert(wire);
            while let Some(wire) = to_visit.pop() {
                if subtree.contains(&wire) {
                    continue;
                }
                subtree.insert(wire);
                if let Some(subs) = tree.get(&wire) {
                    for w in subs.iter() {
                        to_visit.push(*w);
                    }
                } else {
                    assert_eq!(wire.0, 'z');
                }
            }
        } else {
            subtree.insert(wire);
        }
        subtree
    }
}

fn wrong_bit(memo: &mut HashMap<Vec<Wire>, Option<usize>>, swaps: Vec<Wire>) -> Option<usize> {
    unimplemented!()
}

static WIRE_NAMES: OnceLock<HashSet<Wire>> = OnceLock::new();
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
}

impl Puzzle {
    fn search(
        &self,
        level: usize,
        swaps: Vec<(GateSpec, GateSpec)>,
        memo: &mut HashMap<Vec<(GateSpec, GateSpec)>, usize>,
    ) -> Option<Vec<(GateSpec, GateSpec)>> {
        let input_bits = *INPUT_BITS.get().unwrap();
        let relevants = WIRE_NAMES
            .get()
            .unwrap()
            .iter()
            .filter(|wire| wire.0 != 'x' && wire.0 != 'y')
            .filter(|wire| {
                !swaps
                    .iter()
                    .any(|(gs1, gs2)| gs1.3 == **wire || gs2.3 == **wire)
            })
            .sorted()
            .collect::<Vec<_>>();
        let mut to_search: Vec<(Wire, Wire)> = vec![];
        let num_lifts: usize = 0;
        let adder = Adder::new(swaps.clone());
        let wrong_vector = adder.wrong_bits();
        let num_wrong_bits = wrong_vector.iter().filter(|b| **b).count();
        dbg!(relevants.len());
        let (down_tree, up_tree) = adder.wire_trees();
        for (i, pick1) in relevants.iter().enumerate() {
            let _pick1_level = adder
                .wire_affects(&down_tree, **pick1)
                .contains(&bit_to_wire(level, 'z'));
            for pick2 in relevants.iter().skip(i + 1) {
                let _pick2_level = adder
                    .wire_affects(&down_tree, **pick2)
                    .contains(&bit_to_wire(level, 'z'));
                /* if pick1_level || pick2_level */
                {
                    to_search.push((**pick1, **pick2));
                }
            }
        }
        let mut a = (0, 0, 0);
        for (i, case) in to_search.iter().enumerate() {
            // println!("{}-{}", wire_name(pick1), wire_name(pick2));
            // progress!(format!(
            //     "{:>10} level:{level:>2}({i:>5}/{:>5}) lift:{num_lifts:>5}:: {}-{}",
            //     memo.len(),
            //     to_search.len(),
            //     wire_name(&case.0),
            //     wire_name(&case.1)
            // ));
            let mut sw = swaps.clone();
            sw.push(build_swapped_pair(case));
            assert!(sw.len() <= 4);
            let result_vector = Adder::new(sw.clone()).affect_bits(&adder);
            let affects = result_vector.iter().filter(|b| **b).count();
            if 0 < affects {
                a.2 += 1;
                println!("{i:>5}:{}", fmt(&result_vector));
            } else {
                a.1 += 1;
            }
            /*
            let bit = if let Some(b) = memo.get(&sw) {
                *b
            } else {
                let ret = Adder::new(sw.clone()).wrong_bit();
                memo.insert(sw.clone(), ret);
                ret
            };
            if level < bit {
                a.1 += 1;
            } else {
                a.0 += 1;
            }
            */
            // if bit == input_bits + 1 {
            //     assert_eq!(sw.len(), 4);
            //     println!("{sw:?}");
            //     return Some(sw);
            // }
            // if bit <= level {
            //     continue;
            // }
            // num_lifts += 1;
            // if let Some(ret) = self.search(bit, sw, memo) {
            //     return Some(ret);
            // }
        }
        dbg!(a);
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
        let mut wire_names: HashSet<Wire> = HashSet::new();
        for (g, i1, i2, o) in links.iter() {
            wire_names.insert(*i1);
            wire_names.insert(*i2);
            wire_names.insert(*o);
        }
        if WIRE_NAMES.get().is_none() {
            WIRE_NAMES.set(wire_names).unwrap();
        }
        if BASE_LINK.get().is_none() {
            BASE_LINK.set(links).unwrap();
        }
        Self::parsed()
    }
    fn end_of_data(&mut self) {
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
    fn part2(&mut self) -> Self::Output2 {
        let mut memo: HashMap<Vec<(GateSpec, GateSpec)>, usize> = HashMap::new();
        if let Some(vec) = self.search(0, Vec::new(), &mut memo) {
            vec.iter()
                .flat_map(|(gs1, gs2)| vec![wire_name(&gs1.3), wire_name(&gs2.3)])
                .sorted()
                .join(",")
        } else {
            "".to_string()
        }
    }
}
