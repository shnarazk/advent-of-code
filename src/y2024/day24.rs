//! <https://adventofcode.com/2024/day/24>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
#![allow(clippy::type_complexity)]
use {
    crate::{
        color,
        framework::{aoc_at, AdventOfCode, ParseError},
        parser::parse_usize,
        progress,
    },
    itertools::Itertools,
    rayon::{prelude::*, slice::Windows},
    rustc_data_structures::fx::{FxHashMap, FxHashSet, FxHasher},
    serde::{Deserialize, Serialize},
    std::{
        collections::{BinaryHeap, HashMap, HashSet},
        fmt,
        fs::File,
        hash::BuildHasherDefault,
        io::prelude::*,
        sync::OnceLock,
    },
    winnow::{
        ascii::newline,
        combinator::{alt, separated, seq},
        token::one_of,
        PResult, Parser,
    },
};

const PERSISTENT_STORAGE: &'static str = "misc/2024/day24-diff-table.json";

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

fn fmt_(v: &[usize]) -> String {
    format!(
        "{}|{}|0({})",
        v.len(),
        v.iter()
            .rev()
            .map(|n| format!("{n:>2}"))
            .collect::<String>(),
        v.iter().filter(|n| 0 < **n).count(),
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
    (
        prefix,
        (b'0' + ((n / 10) as u8)) as u8,
        (b'0' + ((n % 10) as u8)) as u8,
    )
}

/// convert a `Wire` type to its 'ord', 0 to 43
fn wire_to_ord((_, b, c): &Wire) -> usize {
    (((*b as u8) - b'0') as usize) * 10 + (((*c as u8) - b'0') as usize)
}

/// convert  `Wire` to its string representation
fn wire_to_string((a, b, c): &Wire) -> String {
    format!("{a}{b}{c}")
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
        // let base_config = BASE_LINK.get().unwrap();
        while propagated {
            propagated = false;
            for (gate, output) in self.mapper.iter() {
                match (values.get(&gate.1), values.get(&gate.2), values.get(output)) {
                    (Some(b1), Some(b2), None) => {
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
                    _ => (),
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
        dbg!(fmt(&v));
        let val = v
            .iter()
            .rev()
            .fold(0_usize, |acc, b| acc * 2 + (*b as usize));
        (val, v)
    }
}

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
pub struct Descriptor {
    overrides: Vec<(GateSpec, GateSpec)>,
    width: usize,
}

impl Descriptor {
    fn new(width: usize, overrides: Vec<(GateSpec, GateSpec)>) -> Descriptor {
        Descriptor { overrides, width }
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
        Some(Descriptor::new(self.width, swaps))
    }
    fn build_adder(&self) -> Adder {
        Adder::new(&self.overrides)
    }
    fn check_correctness(&self) -> bool {
        let adder = self.build_adder();
        let input_bits = *INPUT_BITS.get().unwrap();
        (0..input_bits).collect::<Vec<_>>().par_iter().all(|&bit1| {
            let x = 1_usize << bit1;
            (bit1..input_bits).all(|bit2| {
                let y = 1_usize << bit2;
                /* println!(
                    "{} + {} =/{} {}",
                    x % (1 << self.width),
                    y % (1 << self.width),
                    self.width,
                    self.add(x, y).0 % (1 << self.width)
                ); */
                adder.add(x, y).0 % (1 << self.width) == (x + y) % (1 << self.width)
            })
        })
    }
    /// return `(down_tree, up_tree)`
    fn wire_trees(&self) -> (HashMap<Wire, HashSet<Wire>>, HashMap<Wire, HashSet<Wire>>) {
        let adder = self.build_adder();
        let base_links = BASE_LINK.get().unwrap();
        let mut wires: HashSet<Wire> = HashSet::new();
        let mut down_tree: HashMap<Wire, HashSet<Wire>> = HashMap::new();
        let mut up_tree: HashMap<Wire, HashSet<Wire>> = HashMap::new();
        for ((g, i1, i2), o) in adder.mapper.iter() {
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

fn wrong_bit(memo: &mut HashMap<Vec<Wire>, Option<usize>>, swaps: Vec<Wire>) -> Option<usize> {
    unimplemented!()
}

static WIRE_NAMES: OnceLock<HashSet<Wire>> = OnceLock::new();
static BASE_LINK: OnceLock<Vec<(Gate, Wire, Wire, Wire)>> = OnceLock::new();
static INPUT_BITS: OnceLock<usize> = OnceLock::new();
static BASE_OUTPUT: OnceLock<HashMap<(usize, usize), usize>> = OnceLock::new();
static DIFF_MAP: OnceLock<HashMap<(Wire, Wire), Vec<usize>>> = OnceLock::new();
static BASE_PROPAGATION_TABLE: OnceLock<FxHashMap<(Gate, Wire, Wire), Wire>> = OnceLock::new();

fn build_swapped_pair((pick1, pick2): &(Wire, Wire)) -> (GateSpec, GateSpec) {
    assert!(![b'x', b'y'].contains(&pick1.0));
    assert!(![b'x', b'y'].contains(&pick2.0));

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
            .enumerate()
            .map(|(i, (g, i1, i2, o))| {
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
        dbg!(x, y);
        Adder::new(&Vec::new()).add(x, y).0
    }
    fn part2(&mut self) -> Self::Output2 {
        let input_bits = *INPUT_BITS.get().unwrap();
        let wire_names = WIRE_NAMES.get().unwrap();
        let mut to_visit: BinaryHeap<Descriptor> = BinaryHeap::new();
        let adder = Descriptor::new(0, Vec::new());
        to_visit.push(adder);
        let mut visited: HashSet<Descriptor> = HashSet::new();
        let mut best_level: usize = 0;
        while let Some(mut adder) = to_visit.pop() {
            if visited.contains(&adder) {
                continue;
            }
            visited.insert(adder.clone());
            progress!(format!(
                "{:>2} {:>2}-{}/{:>9}",
                best_level,
                adder.width,
                adder.overrides.len(),
                to_visit.len()
            ));
            best_level = best_level.max(adder.width);
            if 40 < adder.width {
                panic!();
            }
            let (d_tree, u_tree) = adder.wire_trees();
            for index in adder.width..(input_bits + 1) {
                adder.width = index;
                if !adder.check_correctness() && adder.overrides.len() < 4 {
                    let input_tree = adder.wire_affects(&u_tree, ord_to_wire(index, b'z'));
                    let inputs = input_tree
                        .iter()
                        .filter(|w| w.0 == b'x' || w.0 == b'y')
                        .sorted()
                        .cloned()
                        .collect::<Vec<_>>();
                    let required = (0..=index)
                        .flat_map(|i| [ord_to_wire(i, b'x'), ord_to_wire(i, b'y')])
                        .collect::<Vec<_>>();
                    let missing = required
                        .iter()
                        .filter(|w| !inputs.contains(w))
                        .cloned()
                        .collect::<Vec<_>>();
                    adder.width -= 1;
                    // println!(
                    //     "bit{}: {:?}",
                    //     index,
                    //     missing.iter().map(wire_to_string).collect::<Vec<_>>()
                    // );
                    // find upper-side nodes (wires)
                    let related_wires = wire_names
                        .iter()
                        .filter(|w| ![b'x', b'y'].contains(&w.0))
                        .filter(|&w| {
                            let w_input_tree = adder.wire_affects(&u_tree, *w);
                            let w_inputs = w_input_tree
                                .iter()
                                .filter(|w| [b'x', b'y'].contains(&w.0))
                                .sorted()
                                .cloned()
                                .collect::<Vec<_>>();
                            let w_output_tree = adder.wire_affects(&d_tree, *w);
                            let w_level = w_output_tree
                                .iter()
                                .filter(|w| w.0 == b'z')
                                .min()
                                .map_or(usize::MAX, |w| wire_to_ord(w));
                            // index <= w_level && w_inputs.iter().all(|w| required.contains(w))
                            w_level <= index
                            // && index <= wire_to_ord(w_outputs.first().unwrap())
                        })
                        .cloned()
                        .collect::<Vec<_>>();
                    for upper in related_wires.iter() {
                        for lower in related_wires.iter() {
                            if let Some(new_adder) = adder.add_swaps(*upper, *lower) {
                                if visited.contains(&new_adder) {
                                    continue;
                                }
                                // println!(
                                //     " - try {index}: {}-{}",
                                //     wire_to_string(upper),
                                //     wire_to_string(lower)
                                // );
                                to_visit.push(new_adder);
                            }
                        }
                    }
                    break;
                }
            }
        }

        "".to_string()

        /*
        if BASE_OUTPUT.get().is_none() {
            let hash = adder.all_outputs();
            let input_bits = *INPUT_BITS.get().unwrap();
            assert_eq!(hash.len(), input_bits * (input_bits - 1) / 2);
            BASE_OUTPUT.set(hash).unwrap();
        }
        self.build_search_table();
        */
    }
}
