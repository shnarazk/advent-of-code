//! <https://adventofcode.com/2024/day/24>
#![allow(clippy::type_complexity)]
use {
    crate::{
        framework::{aoc_at, AdventOfCode, ParseError},
        parser::parse_usize,
        progress,
    },
    itertools::Itertools,
    rayon::prelude::*,
    rustc_data_structures::fx::{FxHashMap, FxHashSet, FxHasher},
    serde::Serialize,
    std::{
        cmp::Reverse,
        collections::{BinaryHeap, HashMap, HashSet},
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

type Wire = (u8, u8, u8);

type GateSpec = (Gate, Wire, Wire, Wire);

/// convert from 'ord', 0 to 43, to wire
fn ord_to_wire(n: usize, prefix: u8) -> Wire {
    (prefix, b'0' + ((n / 10) as u8), b'0' + ((n % 10) as u8))
}

/// convert a `Wire` type to its 'ord', 0 to 43
fn wire_to_ord((_, b, c): &Wire) -> usize {
    ((*b - b'0') as usize) * 10 + ((*c - b'0') as usize)
}

/// convert  `Wire` to its string representation
fn wire_to_string((a, b, c): &Wire) -> String {
    format!("{}{}{}", *a as char, *b as char, *c as char)
}

#[derive(Clone, Debug, Default, Eq, PartialEq, Serialize)]
pub struct Adder {
    mapper: FxHashMap<(Gate, Wire, Wire), Wire>,
}

impl Adder {
    fn new(overrides: &[(GateSpec, GateSpec)]) -> Adder {
        let mut mapper: FxHashMap<(Gate, Wire, Wire), Wire> =
            BASE_PROPAGATION_TABLE.get().unwrap().clone();
        for (g1, g2) in overrides.iter() {
            mapper.insert((g1.0, g1.1, g1.2), g1.3);
            mapper.insert((g2.0, g2.1, g2.2), g2.3);
        }
        Adder { mapper }
    }
    fn add(&self, arg1: usize, arg2: usize) -> (usize, Vec<bool>) {
        let input_bits = *INPUT_BITS.get().unwrap();
        let bit1 = int_to_bit_vector(arg1, input_bits);
        let bit2 = int_to_bit_vector(arg2, input_bits);
        let mut values: FxHashMap<Wire, bool> =
            HashMap::<_, _, BuildHasherDefault<FxHasher>>::default();

        for i in 0..input_bits {
            let wire1 = ord_to_wire(i, b'x');
            values.insert(wire1, bit1.get(i) == Some(&true));
            let wire2 = ord_to_wire(i, b'y');
            values.insert(wire2, bit2.get(i) == Some(&true));
        }

        let mut propagated = true;
        while propagated {
            propagated = false;
            for (gate, output) in self.mapper.iter() {
                if let (Some(b1), Some(b2), None) =
                    (values.get(&gate.1), values.get(&gate.2), values.get(output))
                {
                    values.insert(
                        *output,
                        match gate.0 {
                            Gate::And => b1 & b2,
                            Gate::Or => b1 | b2,
                            Gate::Xor => b1 ^ b2,
                        },
                    );
                    propagated = true;
                }
            }
        }
        let v = values
            .iter()
            .filter(|(wire, _)| wire.0 == b'z') // && wire_to_ord(wire) <= self.width)
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
}

#[derive(Clone, Debug, Default, Eq, Hash, PartialEq, Serialize)]
pub struct Descriptor {
    num_broken: usize,
    overrides: Vec<(GateSpec, GateSpec)>,
}

impl Ord for Descriptor {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        (self.num_broken * self.overrides.len()).cmp(&(other.num_broken * other.overrides.len()))
    }
}

impl PartialOrd for Descriptor {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Descriptor {
    fn new(num_broken: usize, overrides: Vec<(GateSpec, GateSpec)>) -> Descriptor {
        Descriptor {
            num_broken,
            overrides,
        }
    }
    fn add_swaps(&self, w1: Wire, w2: Wire) -> Option<Descriptor> {
        if w1 == w2 {
            return None;
        }
        let mut swaps = self.overrides.clone();
        if swaps
            .iter()
            .any(|pair| [w1, w2].contains(&pair.0 .3) || [w1, w2].contains(&pair.1 .3))
        {
            return None;
        }
        swaps.push(build_swapped_pair(&(w1, w2)));
        swaps.sort_unstable();
        Some(Descriptor::new(self.num_broken, swaps))
    }
    fn build_adder(&self) -> Adder {
        Adder::new(&self.overrides)
    }
    fn check_correctness(&self) -> Option<Vec<usize>> {
        let adder = self.build_adder();
        let input_bits = *INPUT_BITS.get().unwrap();
        let ret = (0..input_bits)
            .collect::<Vec<_>>()
            .par_iter()
            .map(|&bit1| {
                let x = 1_usize << bit1;
                (bit1..input_bits)
                    .map(|bit2| {
                        let y = 1_usize << bit2;
                        /* println!(
                            "{} + {} =/{} {}",
                            x % (1 << self.width),
                            y % (1 << self.width),
                            self.width,
                            self.add(x, y).0 % (1 << self.width)
                        ); */
                        let added = adder.add(x, y).0;
                        (0..=input_bits)
                            .map(|i| {
                                let bit_mask = 1_usize << i;
                                added % bit_mask != (x + y) % bit_mask
                            })
                            .collect::<Vec<_>>()
                    })
                    .fold(vec![0; input_bits + 1], |acc, v| {
                        acc.iter()
                            .zip(v.iter())
                            .map(|(a, b)| a + (*b as usize))
                            .collect::<Vec<_>>()
                    })
            })
            .collect::<Vec<_>>()
            .iter()
            .fold(vec![0; input_bits + 1], |acc, v| {
                acc.iter()
                    .zip(v.iter())
                    .map(|(a, b)| a + *b)
                    .collect::<Vec<_>>()
            });
        let x = 27339360157359;
        let y = 34293989942303;
        let samples = [x, y, 0, 1];
        let one_more = samples
            .iter()
            .map(|a| {
                samples
                    .iter()
                    .map(|b| {
                        let added = adder.add(*a, *b).0;
                        (0..=input_bits)
                            .map(|i| {
                                let bit_mask = 1_usize << i;
                                added % bit_mask != (a + b) % bit_mask
                            })
                            .collect::<Vec<_>>()
                    })
                    .fold(vec![0; input_bits + 1], |acc, v| {
                        acc.iter()
                            .zip(v.iter())
                            .map(|(a, b)| a + (*b as usize))
                            .collect::<Vec<_>>()
                    })
            })
            .fold(vec![0; input_bits], |acc, v| {
                acc.iter()
                    .zip(v.iter())
                    .map(|(a, b)| a + *b)
                    .collect::<Vec<_>>()
            });
        let ret1 = ret
            .iter()
            .zip(one_more.iter())
            .map(|(a, b)| a + *b)
            .collect::<Vec<_>>();
        if ret1.iter().all(|n| *n == 0) {
            None
        } else {
            Some(ret1)
        }
    }
    /// return `(down_tree, up_tree)`
    fn wire_trees(
        &self,
    ) -> (
        FxHashMap<Wire, FxHashSet<Wire>>,
        FxHashMap<Wire, FxHashSet<Wire>>,
    ) {
        let adder = self.build_adder();
        let mut wires: FxHashSet<Wire> = HashSet::<Wire, BuildHasherDefault<FxHasher>>::default();
        let mut down_tree: FxHashMap<Wire, FxHashSet<Wire>> =
            HashMap::<_, _, BuildHasherDefault<FxHasher>>::default();
        let mut up_tree: FxHashMap<Wire, FxHashSet<Wire>> =
            HashMap::<_, _, BuildHasherDefault<FxHasher>>::default();
        for ((_, i1, i2), o) in adder.mapper.iter() {
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
    fn wire_affects(&self, tree: &FxHashMap<Wire, FxHashSet<Wire>>, wire: Wire) -> FxHashSet<Wire> {
        let mut subtree: FxHashSet<Wire> = HashSet::<_, BuildHasherDefault<FxHasher>>::default();
        if let Some(linked) = tree.get(&wire) {
            let mut to_visit: Vec<Wire> = linked.iter().cloned().collect::<Vec<_>>();
            subtree.insert(wire);
            while let Some(w) = to_visit.pop() {
                if subtree.contains(&w) {
                    continue;
                }
                subtree.insert(w);
                if let Some(subs) = tree.get(&w) {
                    for w in subs.iter() {
                        to_visit.push(*w);
                    }
                } else {
                    assert!(
                        [b'x', b'y', b'z'].contains(&w.0),
                        "unlinked wire: {} from {}",
                        wire_to_string(&w),
                        wire_to_string(&wire),
                    );
                }
            }
        } else {
            subtree.insert(wire);
        }
        // assert!(subtree.iter().any(|w| ['x', 'y', 'z'].contains(&w.0)));
        subtree
    }
}

static WIRE_NAMES: OnceLock<HashSet<Wire>> = OnceLock::new();
static BASE_LINK: OnceLock<Vec<(Gate, Wire, Wire, Wire)>> = OnceLock::new();
static INPUT_BITS: OnceLock<usize> = OnceLock::new();
static BASE_PROPAGATION_TABLE: OnceLock<FxHashMap<(Gate, Wire, Wire), Wire>> = OnceLock::new();

fn build_swapped_pair((pick1, pick2): &(Wire, Wire)) -> (GateSpec, GateSpec) {
    assert!(![b'x', b'y'].contains(&pick1.0));
    assert!(![b'x', b'y'].contains(&pick2.0));

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

fn parse_wire(s: &mut &str) -> PResult<Wire> {
    (
        one_of('a'..='z'),
        one_of(('a'..='z', '0'..='9')),
        one_of(('a'..='z', '0'..='9')),
    )
        .map(|(a, b, c)| (a as u8, b as u8, c as u8))
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
        let mut propagation_table: FxHashMap<(Gate, Wire, Wire), Wire> = FxHashMap::default();
        let mut wire_names: HashSet<Wire> = HashSet::new();
        for (g, i1, i2, o) in links.iter() {
            wire_names.insert(*i1);
            wire_names.insert(*i2);
            wire_names.insert(*o);
            propagation_table.insert((*g, *i1, *i2), *o);
        }
        if BASE_PROPAGATION_TABLE.get().is_none() {
            BASE_PROPAGATION_TABLE.set(propagation_table).unwrap();
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
        let input_bits = self.input_wire.iter().filter(|(g, _)| g.0 == b'x').count();
        if INPUT_BITS.get().is_none() {
            INPUT_BITS.set(input_bits).unwrap();
        }
    }
    fn serialize(&self) -> Option<String> {
        let links = BASE_LINK.get().unwrap();
        let mut data = links
            .iter()
            .map(|(_, i1, i2, o)| {
                (
                    wire_to_string(o),
                    vec![wire_to_string(i1), wire_to_string(i2)],
                )
            })
            .collect::<Vec<_>>();
        for (input, _) in self.input_wire.iter() {
            data.push((wire_to_string(input), Vec::new()));
        }
        serde_json::to_string(&data).ok()
    }
    fn part1(&mut self) -> Self::Output1 {
        let x = self
            .input_wire
            .iter()
            .filter(|(wire, _)| wire.0 == b'x')
            .sorted()
            .rev()
            .map(|(_, b)| b)
            .fold(0_usize, |acc, b| acc * 2 + (*b as usize));
        let y = self
            .input_wire
            .iter()
            .filter(|(wire, _)| wire.0 == b'y')
            .sorted()
            .rev()
            .map(|(_, b)| b)
            .fold(0_usize, |acc, b| acc * 2 + (*b as usize));
        Adder::new(&Vec::new()).add(x, y).0
    }
    fn part2(&mut self) -> Self::Output2 {
        let wire_names = WIRE_NAMES.get().unwrap();
        let mut to_visit: BinaryHeap<Reverse<Descriptor>> = BinaryHeap::new();

        let mut init = Descriptor::new(0, Vec::new());
        if let Some(brokens) = init.check_correctness() {
            init.num_broken = brokens.iter().filter(|n| 0 < **n).count();
            to_visit.push(Reverse(init));
        }
        let mut visited: HashSet<Descriptor> = HashSet::new();
        let mut best: usize = 99;
        while let Some(Reverse(mut desc)) = to_visit.pop() {
            if visited.contains(&desc) {
                continue;
            }
            visited.insert(desc.clone());
            best = best.min(desc.num_broken);
            let (d_tree, _) = desc.wire_trees();
            if let Some(brokens) = desc.check_correctness() {
                let num_broken = brokens.iter().filter(|n| 0 < **n).count();
                // if adder.num_broken < num_broken {
                //     continue;
                // }
                desc.num_broken = num_broken;
                progress!(format!(
                    "best:{:>2} broken:{:>2} #swaps:{} |{:>9}| {}",
                    best,
                    desc.num_broken,
                    desc.overrides.len(),
                    visited.len(),
                    fmt(&brokens.iter().map(|n| 0 < *n).collect::<Vec<_>>())
                ));
                let index = brokens.iter().position(|n| 0 < *n).unwrap();
                if desc.overrides.len() < 4 {
                    let related_wires = wire_names
                        .iter()
                        .filter(|w| ![b'x', b'y'].contains(&w.0))
                        .filter(|&w| {
                            let w_output_tree = desc.wire_affects(&d_tree, *w);
                            let w_level = w_output_tree
                                .iter()
                                .filter(|w| w.0 == b'z')
                                .min()
                                .map_or(usize::MAX, wire_to_ord);
                            // index <= w_level && w_inputs.iter().all(|w| required.contains(w))
                            w_level <= index
                            // && index <= wire_to_ord(w_outputs.first().unwrap())
                        })
                        .cloned()
                        .collect::<Vec<_>>();
                    for upper in related_wires.iter() {
                        let from_upper = desc.wire_affects(&d_tree, *upper);
                        for lower in related_wires.iter() {
                            if from_upper.contains(lower) {
                                continue;
                            }
                            let another_tree = desc.wire_affects(&d_tree, *lower);
                            if another_tree.contains(upper) {
                                continue;
                            }
                            if let Some(new_adder) = desc.add_swaps(*upper, *lower) {
                                if visited.contains(&new_adder) {
                                    continue;
                                }
                                to_visit.push(Reverse(new_adder));
                            }
                        }
                    }
                }
            } else {
                let adder = desc.build_adder();
                let x = 27339360157359;
                let y = 34293989942303;
                assert_eq!(adder.add(x, y).0, x + y);
                if adder.add(x, y).0 == x + y
                    && adder.add(y, x).0 == x + y
                    && adder.add(x, 0).0 == x
                    && adder.add(0, y).0 == y
                {
                    desc.num_broken = 0;
                    visited.insert(desc.clone());
                    println!();
                    println!("found!");
                    let ret = desc
                        .overrides
                        .iter()
                        .flat_map(|pair| [pair.0 .3, pair.1 .3])
                        .sorted()
                        .map(|w| wire_to_string(&w))
                        .join(",");
                    println!("\n\n{ret}\n\n");
                }
            }
        }
        "".to_string()
    }
}
