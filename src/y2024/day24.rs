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
        cmp::{Ordering, Reverse},
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
        .expect(format!("wire not found: {}{}", prefix as char, n).as_str())
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
            PROPAGATION_TABLE.get().unwrap().clone();
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
        // (self.num_broken + self.overrides.len() + self.structure)
        //     .cmp(&(other.num_broken + other.overrides.len() + other.structure))
        self.structure.cmp(&other.structure)
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
    fn check_structure(&self) -> Vec<bool> {
        let input_bits = *INPUT_BITS.get().unwrap();
        let up_trees = self.wire_trees(false, true).1.unwrap();
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
        ret
    }
    /// return `(down_tree, up_tree)`
    fn wire_trees(
        &self,
        down: bool,
        up: bool,
    ) -> (
        Option<FxHashMap<&'static Wire, FxHashSet<&'static Wire>>>,
        Option<FxHashMap<&'static Wire, FxHashSet<&'static Wire>>>,
    ) {
        let adder = self.build_adder();
        let mut down_tree: FxHashMap<&'static Wire, FxHashSet<&'static Wire>> =
            HashMap::<_, _, BuildHasherDefault<FxHasher>>::default();
        let mut up_tree: FxHashMap<&'static Wire, FxHashSet<&'static Wire>> =
            HashMap::<_, _, BuildHasherDefault<FxHasher>>::default();
        for ((_, i1, i2), o) in adder.mapper.iter() {
            if down {
                down_tree.entry(*i1).or_default().insert(o);
                down_tree.entry(*i2).or_default().insert(o);
            }
            if up {
                up_tree.entry(*o).or_default().insert(i1);
                up_tree.entry(*o).or_default().insert(i2);
            }
        }
        (down.then_some(down_tree), up.then_some(up_tree))
    }
    fn wire_affects(
        &self,
        tree: &FxHashMap<&'static Wire, FxHashSet<&'static Wire>>,
        wire: &'static Wire,
    ) -> FxHashSet<&'static Wire> {
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
        debug_assert!(subtree.iter().any(|w| [b'x', b'y', b'z'].contains(&w.0)));
        subtree
    }
}

static WIRE_NAMES: OnceLock<FxHashSet<Wire>> = OnceLock::new();
static INPUT_BITS: OnceLock<usize> = OnceLock::new();
static PROPAGATION_TABLE: OnceLock<FxHashMap<(Gate, &'static Wire, &'static Wire), &'static Wire>> =
    OnceLock::new();

fn build_swapped_pair((pick1, pick2): (&'static Wire, &'static Wire)) -> (GateSpec, GateSpec) {
    debug_assert!(![b'x', b'y'].contains(&pick1.0));
    debug_assert!(![b'x', b'y'].contains(&pick2.0));

    let p1 = pick1.min(pick2);
    let p2 = pick1.max(pick2);
    let specs = PROPAGATION_TABLE.get().unwrap();
    let spec1 = specs.iter().find(|(_, o)| **o == p1).unwrap();
    let spec2 = specs.iter().find(|(_, o)| **o == p2).unwrap();
    (
        (spec1.0 .0, spec1.0 .1, spec1.0 .2, p2),
        (spec2.0 .0, spec2.0 .1, spec2.0 .2, p1),
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
        if PROPAGATION_TABLE.get().is_none() {
            PROPAGATION_TABLE.set(propagation_table).unwrap();
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
        let mut data = PROPAGATION_TABLE
            .get()
            .unwrap()
            .iter()
            .map(|((_, i1, i2), o)| {
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
        let input_bits = *INPUT_BITS.get().unwrap();
        let wires = wire_names.iter().collect::<Vec<_>>();
        let mut to_visit: BinaryHeap<Descriptor> = BinaryHeap::new();
        to_visit.push(Descriptor::new(0, 0, Vec::new()));
        let mut visited: FxHashSet<Descriptor> =
            HashSet::<_, BuildHasherDefault<FxHasher>>::default();
        let mut best: usize = 0;
        while let Some(mut desc) = to_visit.pop() {
            if visited.contains(&desc) {
                continue;
            }
            visited.insert(desc.clone());
            let (d_tree, u_tree) = {
                let t = desc.wire_trees(true, true);
                (t.0.unwrap(), t.1.unwrap())
            };
            if let Some(brokens) = desc.check_correctness() {
                let _num_broken = brokens.iter().filter(|n| **n).count();
                let broken_bit = brokens.iter().position(|b| *b).unwrap_or(input_bits + 1);
                let structure = desc.check_structure();
                let _ill_structure_bits = structure.iter().filter(|b| **b).count();
                let ill_structure_bit = structure.iter().position(|b| *b).unwrap_or(input_bits + 1);
                match ill_structure_bit.cmp(&desc.structure) {
                    Ordering::Less => {
                        continue;
                        // if ill_structure_bit < desc.structure {
                        //     continue;
                        // }
                        // desc.num_broken = broken_bit;
                        // desc.structure = ill_structure_bit;
                    }
                    Ordering::Equal => {
                        desc.num_broken = broken_bit;
                        desc.structure = ill_structure_bit;
                    }
                    Ordering::Greater => {
                        // if ill_structure_bit <= desc.structure {
                        //     continue;
                        // }
                        desc.num_broken = broken_bit;
                        desc.structure = ill_structure_bit;
                    }
                }
                best = best.max(desc.num_broken);
                // let structure = 1 /* desc
                //     .check_structure()
                //     .map_or(0, |v| v.iter().filter(|b| **b).count()) */ ;
                // if desc.structure < structure {
                //     continue;
                // }
                // desc.structure = structure;
                progress!(format!(
                    " ❎{:>2}/{:>2}🔄{:>1}📖{:<5} {}",
                    desc.num_broken,
                    best,
                    desc.overrides.len(),
                    visited.len(),
                    fmt(&structure) // fmt(&brokens)
                ));
                let index = ill_structure_bit.min(broken_bit); // brokens.iter().position(|b| *b).unwrap();
                if desc.overrides.len() < 4 {
                    let cones = build_cones(&d_tree, &wires);
                    // I don't know how to use this condition.
                    let strict_mode = {
                        // let wrong_bit = brokens.iter().position(|b| *b).unwrap();
                        // let invalid_bit = structure.iter().position(|b| *b).unwrap();
                        // wrong_bit == invalid_bit
                        ill_structure_bit == broken_bit
                    };
                    let related_wires = if ill_structure_bit <= broken_bit {
                        let up_tree =
                            desc.wire_affects(&u_tree, ord_to_wire(ill_structure_bit, b'z'));
                        let inputs = up_tree
                            .iter()
                            .filter(|w| [b'x', b'y'].contains(&w.0))
                            .cloned()
                            .collect::<Vec<_>>();
                        let targets1 = up_tree
                            .iter()
                            .filter(|w| ![b'x', b'y'].contains(&w.0))
                            .cloned()
                            .collect::<HashSet<_>>();
                        let missing_lowest_input = (0..=ill_structure_bit)
                            .flat_map(|n| {
                                if n < input_bits {
                                    vec![ord_to_wire(n, b'x'), ord_to_wire(n, b'y')]
                                } else {
                                    Vec::new()
                                }
                            })
                            .filter(|w| !inputs.contains(w))
                            .sorted()
                            .min()
                            .unwrap();
                        let down_tree = desc.wire_affects(&d_tree, missing_lowest_input);
                        let targets2 = down_tree
                            .iter()
                            .filter(|w| ![b'x', b'y'].contains(&w.0))
                            .cloned()
                            .collect::<HashSet<_>>();
                        let extra_inputs = (ill_structure_bit + 1..input_bits)
                            .flat_map(|n| [ord_to_wire(n, b'x'), ord_to_wire(n, b'y')])
                            .filter(|w| {
                                cones
                                    .get(w)
                                    .unwrap()
                                    .contains(&ord_to_wire(ill_structure_bit, b'z'))
                            })
                            .collect::<Vec<_>>();
                        println!(
                            "{:?}: target1:{:?}target2:{:?}",
                            up_tree
                                .iter()
                                .map(|w| wire_to_string(w))
                                .collect::<Vec<_>>(),
                            targets1
                                .iter()
                                .map(|w| wire_to_string(w))
                                .collect::<Vec<_>>(),
                            targets2
                                .iter()
                                .map(|w| wire_to_string(w))
                                .collect::<Vec<_>>()
                        );
                        // assert!(!extra_inputs.is_empty());
                        targets1.union(&targets2).map(|f| *f).collect::<Vec<_>>()
                    } else {
                        wire_names
                            .iter()
                            .filter(|w| ![b'x', b'y'].contains(&w.0))
                            .filter(|&w| {
                                cones
                                    .get(w)
                                    .unwrap()
                                    .iter()
                                    .filter(|w| w.0 == b'z')
                                    .min()
                                    .map_or(usize::MAX, |w| wire_to_ord(w))
                                    <= index
                            })
                            .map(|f| f)
                            .collect::<Vec<_>>()
                    };
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
                                && !cone1.contains(output_wire)
                                && !cone2.contains(output_wire)
                            {
                                continue;
                            }
                            if let Some(new_desc) = desc.add_swaps(wire1, wire2) {
                                if !visited.contains(&new_desc) {
                                    to_visit.push(new_desc);
                                }
                            }
                        }
                    }
                }
            } else if desc.check_structure().iter().all(|b| !*b) {
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
