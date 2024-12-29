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

type GateSpec = (Gate, &'static Wire, &'static Wire, &'static Wire);

/// convert from 'ord', 0 to 43, to wire
fn ord_to_wire(n: usize, prefix: u8) -> &'static Wire {
    let wire_names = WIRE_NAMES.get().unwrap();
    wire_names
        .get(&(prefix, b'0' + ((n / 10) as u8), b'0' + ((n % 10) as u8)))
        .unwrap()
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
    mapper: FxHashMap<(Gate, &'static Wire, &'static Wire), &'static Wire>,
}

impl Adder {
    fn new(overrides: &[(GateSpec, GateSpec)]) -> Adder {
        let mut mapper: FxHashMap<(Gate, &'static Wire, &'static Wire), &'static Wire> =
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
        let mut values: FxHashMap<&'static Wire, bool> =
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
    structure: usize,
}

impl Ord for Descriptor {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        (self.num_broken + self.overrides.len() + self.structure)
            .cmp(&(other.num_broken + other.overrides.len() + other.structure))
    }
}

impl PartialOrd for Descriptor {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Descriptor {
    fn new(
        num_broken: usize,
        structure: usize,
        overrides: Vec<(GateSpec, GateSpec)>,
    ) -> Descriptor {
        Descriptor {
            num_broken,
            overrides,
            structure,
        }
    }
    fn add_swaps(&self, w1: &'static Wire, w2: &'static Wire) -> Option<Descriptor> {
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
        swaps.push(build_swapped_pair((w1, w2)));
        swaps.sort_unstable();
        Some(Descriptor::new(self.num_broken, self.structure, swaps))
    }
    fn build_adder(&self) -> Adder {
        Adder::new(&self.overrides)
    }
    fn check_correctness(&self) -> Option<Vec<bool>> {
        fn merge_or(acc: Vec<bool>, v: Vec<bool>) -> Vec<bool> {
            acc.iter()
                .zip(v.iter())
                .map(|(a, b)| *a || *b)
                .collect::<Vec<_>>()
        }
        let adder = self.build_adder();
        let input_bits = *INPUT_BITS.get().unwrap();
        let ret: Vec<bool> = (0..=input_bits)
            .collect::<Vec<_>>()
            .par_iter()
            .map(|&bit1| {
                let x = (1_usize << bit1) * ((bit1 < input_bits) as usize);
                (bit1..input_bits)
                    .map(|bit2| {
                        let y = 1_usize << bit2;
                        let added = adder.add(x, y).0;
                        (0..=input_bits)
                            .map(|i| {
                                let bit_mask = 1_usize << i;
                                added % bit_mask != (x + y) % bit_mask
                            })
                            .collect::<Vec<_>>()
                    })
                    .fold(vec![false; input_bits + 1], merge_or)
            })
            .collect::<Vec<_>>()
            .iter()
            .cloned()
            .fold(vec![false; input_bits + 1], merge_or);
        if ret.iter().all(|n| !*n) {
            None
        } else {
            Some(ret)
        }
    }
    /// return a vector of wrong structure bools
    /// This measure doesn't return mono-decreasing values
    /// So we can't use to cut branches. This is the final checker.
    fn check_structure(&self) -> Option<Vec<bool>> {
        let input_bits = *INPUT_BITS.get().unwrap();
        let (_, up_trees) = self.wire_trees();
        let mut ret = (0..input_bits)
            .collect::<Vec<_>>()
            .par_iter()
            .map(|&n| {
                let wire: &'static Wire = ord_to_wire(n, b'z');
                let up_tree: FxHashSet<&Wire> = self.wire_affects(&up_trees, wire);
                let inputs: Vec<&Wire> = up_tree
                    .iter()
                    .filter(|w| [b'x', b'y'].contains(&w.0))
                    .cloned()
                    .collect::<Vec<_>>();
                inputs.iter().any(|w| n < wire_to_ord(w)) || inputs.len() != 2 * (n + 1)
            })
            .collect::<Vec<bool>>();

        let carry_bit = {
            let n = input_bits;
            let wire: &'static Wire = ord_to_wire(n, b'z');
            let up_tree = self.wire_affects(&up_trees, wire);
            let input_len = up_tree
                .iter()
                .filter(|w| [b'x', b'y'].contains(&w.0))
                .count();
            input_len != 2 * n
        };
        ret.push(carry_bit);
        if ret.iter().all(|b| !b) {
            None
        } else {
            Some(ret)
        }
    }
    /// return `(down_tree, up_tree)`
    fn wire_trees(
        &self,
    ) -> (
        FxHashMap<&'static Wire, FxHashSet<&'static Wire>>,
        FxHashMap<&'static Wire, FxHashSet<&'static Wire>>,
    ) {
        let adder = self.build_adder();
        let mut wires: FxHashSet<&'static Wire> =
            HashSet::<&'static Wire, BuildHasherDefault<FxHasher>>::default();
        let mut down_tree: FxHashMap<&'static Wire, FxHashSet<&'static Wire>> =
            HashMap::<_, _, BuildHasherDefault<FxHasher>>::default();
        let mut up_tree: FxHashMap<&'static Wire, FxHashSet<&'static Wire>> =
            HashMap::<_, _, BuildHasherDefault<FxHasher>>::default();
        for ((_, i1, i2), o) in adder.mapper.iter() {
            wires.insert(*i1);
            wires.insert(*i2);
            wires.insert(*o);
            down_tree.entry(*i1).or_default().insert(o);
            down_tree.entry(*i2).or_default().insert(o);
            up_tree.entry(*o).or_default().insert(i1);
            up_tree.entry(*o).or_default().insert(i2);
        }
        (down_tree, up_tree)
    }
    fn wire_affects(
        &self,
        tree: &FxHashMap<&'static Wire, FxHashSet<&'static Wire>>,
        wire: &'static Wire,
    ) -> FxHashSet<&Wire> {
        let mut subtree: FxHashSet<&Wire> = HashSet::<_, BuildHasherDefault<FxHasher>>::default();
        if let Some(linked) = tree.get(&wire) {
            let mut to_visit: Vec<&Wire> = linked.iter().cloned().collect::<Vec<_>>();
            subtree.insert(wire);
            while let Some(w) = to_visit.pop() {
                if subtree.contains(&w) {
                    continue;
                }
                subtree.insert(w);
                if let Some(subs) = tree.get(&w) {
                    for w in subs.iter() {
                        to_visit.push(w);
                    }
                } else {
                    debug_assert!(
                        [b'x', b'y', b'z'].contains(&w.0),
                        "unlinked wire: {} from {}",
                        wire_to_string(w),
                        wire_to_string(wire),
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

static WIRE_NAMES: OnceLock<FxHashSet<Wire>> = OnceLock::new();
static BASE_LINK: OnceLock<Vec<(Gate, &'static Wire, &'static Wire, &'static Wire)>> =
    OnceLock::new();
static INPUT_BITS: OnceLock<usize> = OnceLock::new();
static BASE_PROPAGATION_TABLE: OnceLock<
    FxHashMap<(Gate, &'static Wire, &'static Wire), &'static Wire>,
> = OnceLock::new();

fn build_swapped_pair((pick1, pick2): (&'static Wire, &'static Wire)) -> (GateSpec, GateSpec) {
    assert!(![b'x', b'y'].contains(&pick1.0));
    assert!(![b'x', b'y'].contains(&pick2.0));

    let p1 = pick1.min(pick2);
    let p2 = pick1.max(pick2);
    let specs = BASE_LINK.get().unwrap();
    let spec1: &GateSpec = specs.iter().find(|(_, _, _, o)| *o == p1).unwrap();
    let spec2: &GateSpec = specs.iter().find(|(_, _, _, o)| *o == p2).unwrap();
    (
        (spec1.0, spec1.1, spec1.2, p2),
        (spec2.0, spec2.1, spec2.2, p1),
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
        let mut wire_names_tmp: FxHashSet<Wire> =
            HashSet::<_, BuildHasherDefault<FxHasher>>::default();
        for (_, i1, i2, o) in links.iter() {
            wire_names_tmp.insert(*i1);
            wire_names_tmp.insert(*i2);
            wire_names_tmp.insert(*o);
            // propagation_table.insert((*g, i1, i2), o);
        }
        if WIRE_NAMES.get().is_none() {
            WIRE_NAMES.set(wire_names_tmp).unwrap();
        }
        let wire_names: &'static FxHashSet<Wire> = WIRE_NAMES.get().unwrap();
        let mut propagation_table: FxHashMap<(Gate, &'static Wire, &'static Wire), &'static Wire> =
            FxHashMap::default();
        for (g, i1, i2, o) in links.iter() {
            propagation_table.insert(
                (*g, wire_names.get(i1).unwrap(), wire_names.get(i2).unwrap()),
                wire_names.get(o).unwrap(),
            );
        }
        if BASE_PROPAGATION_TABLE.get().is_none() {
            BASE_PROPAGATION_TABLE.set(propagation_table).unwrap();
        }
        let linkp: Vec<GateSpec> = links
            .iter()
            .map(|(g, i1, i2, o)| {
                (
                    *g,
                    wire_names.get(i1).unwrap(),
                    wire_names.get(i2).unwrap(),
                    wire_names.get(o).unwrap(),
                )
            })
            .collect::<Vec<(Gate, _, _, _)>>();
        if BASE_LINK.get().is_none() {
            BASE_LINK.set(linkp).unwrap();
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
        let input_bits = INPUT_BITS.get().unwrap();
        let wires = wire_names.iter().collect::<Vec<_>>();
        let mut to_visit: BinaryHeap<Reverse<Descriptor>> = BinaryHeap::new();

        let mut init = Descriptor::new(0, input_bits + 1, Vec::new());
        if let Some(brokens) = init.check_correctness() {
            // dbg!(fmt(&init.check_connectivity().unwrap()));
            // init.num_broken = brokens.iter().filter(|n| 0 < **n).count();
            init.num_broken = brokens.len() + 1;
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
            let (d_tree, _u_tree) = desc.wire_trees();
            if let Some(brokens) = desc.check_correctness() {
                let num_broken = brokens.iter().filter(|n| **n).count();
                if desc.num_broken < num_broken {
                    continue;
                }
                desc.num_broken = num_broken;
                desc.structure = desc
                    .check_structure()
                    .map_or(0, |v| v.iter().filter(|b| **b).count());
                progress!(format!(
                    "best:{:>2} broken:{:>2} #swaps:{} |{:>6}| {}",
                    best,
                    desc.num_broken,
                    desc.overrides.len(),
                    visited.len(),
                    fmt(&brokens)
                ));
                let index = brokens.iter().position(|b| *b).unwrap();
                if desc.overrides.len() < 4 {
                    let cones = build_cones(&d_tree, &wires);
                    let strict_mode = {
                        let wrong_bit = brokens.iter().position(|b| *b).unwrap();
                        let invalid_bit = desc
                            .check_structure()
                            .map_or_else(|| 0, |v| v.iter().position(|b| *b).unwrap());
                        wrong_bit == invalid_bit
                    };
                    let related_wires = wire_names
                        .iter()
                        .filter(|w| ![b'x', b'y'].contains(&w.0))
                        .filter(|&w| {
                            let cone = cones.get(w).unwrap();
                            let w_level = cone
                                .iter()
                                .filter(|w| w.0 == b'z')
                                .min()
                                .map_or(usize::MAX, |w| wire_to_ord(w));
                            w_level <= index
                        })
                        .collect::<Vec<_>>();
                    let output_wire = ord_to_wire(index, b'z');
                    for wire1 in related_wires.iter() {
                        let cone1 = cones.get(wire1).unwrap();
                        for wire2 in related_wires.iter() {
                            if cone1.contains(wire2) {
                                continue;
                            }
                            let cone2 = cones.get(wire2).unwrap();
                            if cone2.contains(wire1) {
                                continue;
                            }
                            if strict_mode
                                && !cone1.iter().any(|w| *w == output_wire)
                                && !cone2.iter().any(|w| *w == output_wire)
                            {
                                continue;
                            }
                            if let Some(new_adder) = desc.add_swaps(wire1, wire2) {
                                if visited.contains(&new_adder) {
                                    continue;
                                }
                                to_visit.push(Reverse(new_adder));
                            }
                        }
                    }
                }
            } else if desc.check_structure().is_none() {
                progress!("");
                return desc
                    .overrides
                    .iter()
                    .flat_map(|pair| [pair.0 .3, pair.1 .3])
                    .sorted()
                    .map(wire_to_string)
                    .join(",");
            }
        }
        unreachable!()
    }
}

fn build_cones(
    tree: &FxHashMap<&'static Wire, FxHashSet<&'static Wire>>,
    wires: &[&'static Wire],
) -> FxHashMap<&'static Wire, FxHashSet<&'static Wire>> {
    fn aux<'a, 'b>(
        result: &'b mut FxHashMap<&'static Wire, FxHashSet<&'static Wire>>,
        tree: &'a FxHashMap<&'static Wire, FxHashSet<&'static Wire>>,
        wire: &'static Wire,
    ) -> &'b FxHashSet<&'static Wire>
    where
        'b: 'a,
    {
        if !result.contains_key(wire) {
            let mut entry: FxHashSet<&'static Wire> =
                HashSet::<_, BuildHasherDefault<FxHasher>>::default();
            entry.insert(wire);
            if let Some(childs) = tree.get(wire) {
                for w in childs.iter() {
                    entry.insert(*w);
                    for s in aux(result, tree, w) {
                        entry.insert(*s);
                    }
                }
            }
            result.insert(wire, entry);
        }
        result.get(wire).unwrap()
    }
    wires.iter().fold(
        HashMap::<&'static Wire, FxHashSet<&'static Wire>, BuildHasherDefault<FxHasher>>::default(),
        |mut acc, wire| {
            let _ = aux(&mut acc, tree, wire);
            debug_assert!(acc.contains_key(wire));
            acc
        },
    )
}
