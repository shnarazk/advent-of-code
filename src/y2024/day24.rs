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

type GateSpec = (&'static Wire, (Gate, &'static Wire, &'static Wire));

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
    dep_graph: FxHashMap<&'static Wire, (Gate, &'static Wire, &'static Wire)>,
}

impl Adder {
    fn new(overrides: &[(GateSpec, GateSpec)]) -> Adder {
        let mut dep_graph: FxHashMap<&'static Wire, (Gate, &'static Wire, &'static Wire)> =
            PROPAGATION_TABLE.get().unwrap().clone();
        for ((g1_out, g1), (g2_out, g2)) in overrides.iter() {
            dep_graph.insert(*g1_out, *g2);
            dep_graph.insert(*g2_out, *g1);
        }
        Adder { dep_graph }
    }
    fn add(&self, arg1: usize, arg2: usize) -> (usize, Vec<bool>) {
        let input_bits = *INPUT_BITS.get().unwrap();
        let bit1 = int_to_bit_vector(arg1, input_bits);
        let bit2 = int_to_bit_vector(arg2, input_bits);
        let mut values: FxHashMap<&'static Wire, Option<bool>> =
            HashMap::<_, _, BuildHasherDefault<FxHasher>>::default();

        for i in 0..input_bits {
            let wire1 = ord_to_wire(i, b'x');
            values.insert(wire1, Some(bit1.get(i) == Some(&true)));
            let wire2 = ord_to_wire(i, b'y');
            values.insert(wire2, Some(bit2.get(i) == Some(&true)));
        }
        fn gate_output(
            dep_graph: &FxHashMap<&'static Wire, (Gate, &'static Wire, &'static Wire)>,
            values: &mut FxHashMap<&'static Wire, Option<bool>>,
            wire: &'static Wire,
        ) -> Option<bool> {
            // dbg!(wire_to_string(wire));
            if let Some(b) = values.get(wire) {
                if b.is_none() {
                    return None;
                }
                return *b;
            }
            let Some((g, w1, w2)) = dep_graph.get(wire) else {
                // panic!("gate_output: {}", wire_to_string(wire));
                return None;
            };
            values.insert(wire, None);
            let b1 = gate_output(dep_graph, values, w1)?;
            let b2 = gate_output(dep_graph, values, w2)?;
            let b = match g {
                Gate::And => b1 & b2,
                Gate::Or => b1 | b2,
                Gate::Xor => b1 ^ b2,
            };
            values.insert(wire, Some(b));
            Some(b)
        }
        (0..=input_bits).for_each(|i| {
            gate_output(&self.dep_graph, &mut values, ord_to_wire(i, b'z'));
        });
        let v = (0..=input_bits)
            .map(|i| {
                values
                    .get(ord_to_wire(i, b'z'))
                    .map_or(false, |b| b.map_or(false, |b| b))
            })
            .collect::<Vec<_>>();
        // let v = values
        //     .iter()
        //     .filter(|(wire, _)| wire.0 == b'z') // && wire_to_ord(wire) <= self.width)
        //     .sorted()
        //     .map(|(_, b)| b)
        //     .cloned()
        //     .collect::<Vec<bool>>();
        let val = v
            .iter()
            .rev()
            .fold(0_usize, |acc, b| acc * 2 + (*b as usize));
        (val, v)
    }
}

#[derive(Clone, Debug, Default, Eq, Hash, PartialEq, Serialize)]
pub struct Descriptor {
    target_vector: Vec<bool>,
    overrides: Vec<(GateSpec, GateSpec)>,
}

impl Ord for Descriptor {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        match (
            self.target_vector
                .iter()
                .enumerate()
                .all(|(i, b)| !*b || other.target_vector[i]),
            other
                .target_vector
                .iter()
                .enumerate()
                .all(|(i, b)| !*b || self.target_vector[i]),
        ) {
            (true, true) => Ordering::Equal,
            (true, false) => Ordering::Less,
            (false, true) => Ordering::Greater,
            (false, false) => other.first_target().cmp(&self.first_target()),
        }
    }
}

impl PartialOrd for Descriptor {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl std::fmt::Display for Descriptor {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "({}){}",
            self.number_of_targets(),
            fmt(&self.target_vector)
        )
    }
}

impl Descriptor {
    fn new(overrides: Vec<(GateSpec, GateSpec)>) -> Descriptor {
        Descriptor {
            target_vector: Vec::new(),
            overrides,
        }
    }
    fn evaluate(&mut self) {
        self.target_vector = self
            .check_correctness()
            // .iter()
            // .zip(self.check_structure().iter())
            // .map(|(a, b)| *a || !*b)
            // .collect();
            ;
    }
    fn add_swaps(&self, w1: &'static Wire, w2: &'static Wire) -> Option<Descriptor> {
        if w1 == w2 {
            return None;
        }
        let mut swaps = self.overrides.clone();
        if swaps
            .iter()
            .any(|pair| [w1, w2].contains(&pair.0 .0) || [w1, w2].contains(&pair.1 .0))
        {
            return None;
        }
        swaps.push(build_swapped_pair((w1, w2)));
        swaps.sort_unstable();
        Some(Descriptor::new(swaps))
    }
    fn build_adder(&self) -> Adder {
        Adder::new(&self.overrides)
    }
    fn check_correctness(&self) -> Vec<bool> {
        fn merge_or(acc: Vec<bool>, v: Vec<bool>) -> Vec<bool> {
            acc.iter()
                .zip(v.iter())
                .map(|(a, b)| *a || *b)
                .collect::<Vec<_>>()
        }
        let adder = self.build_adder();
        let input_bits = *INPUT_BITS.get().unwrap();
        (0..=input_bits)
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
                                added & bit_mask != (x + y) & bit_mask
                            })
                            .collect::<Vec<_>>()
                    })
                    .fold(vec![false; input_bits + 1], merge_or)
            })
            .collect::<Vec<_>>()
            .iter()
            .cloned()
            .fold(vec![false; input_bits + 1], merge_or)
    }
    /// return a vector of wrong structure bools
    /// This measure doesn't return mono-decreasing values
    /// So we can't use to cut branches. This is the final checker.
    #[allow(dead_code)]
    fn check_structure(&self) -> Vec<bool> {
        let input_bits = *INPUT_BITS.get().unwrap();
        let (_, up_trees) = self.wire_trees(false, true);
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
    #[allow(dead_code)]
    fn wire_trees(
        &self,
        down: bool,
        up: bool,
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
        for (o, (_, i1, i2)) in adder.dep_graph.iter() {
            wires.insert(*i1);
            wires.insert(*i2);
            wires.insert(*o);
            if down {
                down_tree.entry(*i1).or_default().insert(o);
                down_tree.entry(*i2).or_default().insert(o);
            }
            if up {
                up_tree.entry(*o).or_default().insert(i1);
                up_tree.entry(*o).or_default().insert(i2);
            }
        }
        (down_tree, up_tree)
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
    /// return the first broken bit
    fn first_target(&self) -> usize {
        self.target_vector.iter().position(|n| *n).unwrap()
    }
    /// return the number of broken bits
    fn number_of_targets(&self) -> usize {
        self.target_vector.iter().filter(|b| **b).count()
    }
}

static WIRE_NAMES: OnceLock<FxHashSet<Wire>> = OnceLock::new();
static INPUT_BITS: OnceLock<usize> = OnceLock::new();
static PROPAGATION_TABLE: OnceLock<FxHashMap<&'static Wire, (Gate, &'static Wire, &'static Wire)>> =
    OnceLock::new();

fn build_swapped_pair((pick1, pick2): (&'static Wire, &'static Wire)) -> (GateSpec, GateSpec) {
    debug_assert!(![b'x', b'y'].contains(&pick1.0));
    debug_assert!(![b'x', b'y'].contains(&pick2.0));

    let p1 = pick1.min(pick2);
    let p2 = pick1.max(pick2);
    let specs = PROPAGATION_TABLE.get().unwrap();
    let spec1 = specs.iter().find(|(o, _)| **o == p1).unwrap();
    let spec2 = specs.iter().find(|(o, _)| **o == p2).unwrap();
    (
        (p1, (spec1.1 .0, spec1.1 .1, spec1.1 .2)),
        (p2, (spec2.1 .0, spec2.1 .1, spec2.1 .2)),
        // (p2, (spec1.1 .0, spec1.1 .1, spec1.1 .2)),
        // (p1, (spec2.1 .0, spec2.1 .1, spec2.1 .2)),
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
        let mut propagation_table: FxHashMap<&'static Wire, (Gate, &'static Wire, &'static Wire)> =
            FxHashMap::default();
        for (g, i1, i2, o) in links.iter() {
            propagation_table.insert(
                wire_names.get(o).unwrap(),
                (*g, wire_names.get(i1).unwrap(), wire_names.get(i2).unwrap()),
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
            .map(|(o, (_, i1, i2))| {
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
        let propagation_table = PROPAGATION_TABLE.get().unwrap();
        let wire_names = WIRE_NAMES.get().unwrap();
        let wires = wire_names.iter().collect::<Vec<_>>();

        let mut step0 = Descriptor::new(vec![]);
        step0.evaluate();
        println!("initial:{}", fmt(&step0.target_vector));
        println!("       :{}", fmt(&step0.check_structure()));

        let z05 = propagation_table
            .get_key_value(&(b'z', b'0', b'5'))
            .unwrap();
        let gdd = propagation_table
            .get_key_value(&(b'g', b'd', b'd'))
            .unwrap();

        let Some(mut step1) = step0.add_swaps(*z05.0, *gdd.0) else {
            panic!();
        };
        step1.evaluate();
        println!("z05-gdd:{}", fmt(&step1.target_vector));
        println!("       :{}", fmt(&step1.check_structure()));

        let z09 = propagation_table
            .get_key_value(&(b'z', b'0', b'9'))
            .unwrap();
        let cwt = propagation_table
            .get_key_value(&(b'c', b'w', b't'))
            .unwrap();

        let Some(mut step2) = step1.add_swaps(*z09.0, *cwt.0) else {
            panic!();
        };
        step2.evaluate();
        println!("z09-cwt:{}", fmt(&step2.target_vector));
        println!("       :{}", fmt(&step2.check_structure()));

        let css = propagation_table
            .get_key_value(&(b'c', b's', b's'))
            .unwrap();
        let jmv = propagation_table
            .get_key_value(&(b'j', b'm', b'v'))
            .unwrap();

        let Some(mut step3) = step2.add_swaps(*css.0, *jmv.0) else {
            panic!();
        };
        step3.evaluate();
        println!("css-jmv:{}", fmt(&step3.target_vector));
        println!("       :{}", fmt(&step3.check_structure()));

        let z37 = propagation_table
            .get_key_value(&(b'z', b'3', b'7'))
            .unwrap();

        let pqt = propagation_table
            .get_key_value(&(b'p', b'q', b't'))
            .unwrap();

        let Some(mut step4) = step3.add_swaps(*z37.0, *pqt.0) else {
            panic!();
        };
        step4.evaluate();
        println!("z37-pqt:{}", fmt(&step4.target_vector));
        println!("       :{}", fmt(&step4.check_structure()));

        // return "not implemented".to_string();

        // dbg!(fmt(&step1.target_vector));
        // let mut jmv = Descriptor::new(vec![((*z05.0, *z05.1), (*jmv.0, *jmv.1))]);
        // jmv.evaluate();
        // dbg!(fmt(&jmv.target_vector));
        // let mut pqt = Descriptor::new(vec![((*z05.0, *z05.1), (*pqt.0, *pqt.1))]);
        // pqt.evaluate();
        // dbg!(fmt(&pqt.target_vector));
        // let gdd = propagation_table
        //     .get_key_value(&(b'g', b'd', b'd'))
        //     .unwrap();

        // let mut init = Descriptor::new(Vec::new());
        // let (d_tree, u_tree) = init.wire_trees(true, true);
        // let inputs = init.wire_affects(&u_tree, wire_names.get(&(b'g', b'd', b'd')).unwrap());
        // dbg!(inputs
        //     .iter()
        //     .filter(|w| [b'x', b'y'].contains(&w.0))
        //     .map(|w| wire_to_string(w))
        //     .collect::<Vec<_>>());

        // let outputs = init.wire_affects(&d_tree, wire_names.get(&(b'g', b'd', b'd')).unwrap());
        // dbg!(outputs
        //     .iter()
        //     .filter(|w| [b'z'].contains(&w.0))
        //     .map(|w| wire_to_string(w))
        //     .collect::<Vec<_>>());
        // return "not implemented".to_string();

        let mut generated = 0;
        let _input_bits = INPUT_BITS.get().unwrap();
        let mut to_visit: BinaryHeap<Reverse<Descriptor>> = BinaryHeap::new();
        let mut init = Descriptor::new(Vec::new());
        init.evaluate();
        dbg!(fmt(&init.target_vector));
        to_visit.push(Reverse(init));
        // if let Some(brokens) = init.check_correctness() {
        // init.num_broken = brokens.iter().filter(|n| 0 < **n).count();
        // }
        let mut visited: FxHashSet<Descriptor> =
            HashSet::<_, BuildHasherDefault<FxHasher>>::default();
        let mut best: usize = 99;
        while let Some(Reverse(desc)) = to_visit.pop() {
            if generated == 221 {
                // dbg!(desc.first_target());
                // let index = desc.first_target();
                // let (_d_tree, u_tree) = desc.wire_trees(false, true);
                // let inputs = desc
                //     .wire_affects(&u_tree, ord_to_wire(index, b'z'))
                //     .iter()
                //     .filter(|w| ![b'x', b'y'].contains(&w.0))
                //     .map(|w| wire_to_string(w))
                //     .collect::<Vec<_>>();
                // dbg!(inputs);
                // dbg!(desc.number_of_targets());
                // panic!();
            }
            if desc.number_of_targets() == 0 {
                progress!("");
                println!("{desc}");
                // if desc.check_structure().iter().any(|b| *b) {
                //     continue;
                // }
                return desc
                    .overrides
                    .iter()
                    .flat_map(|pair| [pair.0 .0, pair.1 .0])
                    // .sorted()
                    .map(wire_to_string)
                    .join(",");
            }
            if visited.contains(&desc) || 4 <= desc.overrides.len() {
                continue;
            }
            best = best.min(desc.number_of_targets());
            let index = desc.first_target();
            // assert!(index <= 5);
            let (d_tree, u_tree) = desc.wire_trees(true, true);
            // FIXME: 以下は構造検査を有効にするまで妥当ではない
            // assert!((0..index).all(|i| desc
            //     .wire_affects(&u_tree, ord_to_wire(i, b'z'))
            //     .iter()
            //     .filter(|w| [b'x', b'y'].contains(&w.0))
            //     .count()
            //     == (i + 1) * 2));
            // assert!(
            //     desc.wire_affects(&u_tree, ord_to_wire(index, b'z'))
            //         .iter()
            //         .filter(|w| [b'x', b'y'].contains(&w.0))
            //         .count()
            //         != (index + 1) * 2,
            //     "aa{} {}",
            //     index,
            //     desc.wire_affects(&u_tree, ord_to_wire(index, b'z'))
            //         .iter()
            //         .filter(|w| [b'x', b'y'].contains(&w.0))
            //         .count()
            // );
            let related_wires = desc
                .wire_affects(&u_tree, ord_to_wire(index, b'z'))
                .iter()
                .filter(|w| ![b'x', b'y'].contains(&w.0))
                .cloned()
                .collect::<Vec<_>>();
            assert!(related_wires.contains(&ord_to_wire(index, b'z')));
            let _output_wire = ord_to_wire(index, b'z');
            let cones = build_cones(&d_tree, &wires);
            // if generated == 221 {
            //     println!(
            //         "related_wires: {}",
            //         related_wires.iter().map(|w| wire_to_string(w)).join(", ")
            //     );
            // }
            for &wire1 in related_wires.iter() {
                let cone1 = cones.get(wire1).unwrap();
                for wire2 in wire_names.iter() {
                    if [b'x', b'y'].contains(&wire2.0) {
                        continue;
                    }
                    if cone1.contains(wire2) {
                        continue;
                    }
                    let cone2 = cones.get(wire2).unwrap();
                    if cone2.contains(wire1) {
                        continue;
                    }
                    if let Some(mut new_desc) = desc.add_swaps(wire1, wire2) {
                        if !visited.contains(&new_desc) {
                            new_desc.evaluate();
                            if new_desc <= desc {
                                // if false
                                //     && *wire1 == (b'z', b'0', b'5')
                                //     && *wire2 == (b'g', b'd', b'd')
                                // {
                                //     dbg!();
                                //     dbg!(format!("{}", desc));
                                //     dbg!(format!("{}", new_desc));
                                //     dbg!(desc.overrides.len());
                                //     dbg!(new_desc.overrides.len());
                                //     dbg!(new_desc.cmp(&desc));
                                //     let mut gdd_desc =
                                //         Descriptor::new(vec![((*z05.0, *z05.1), (*gdd.0, *gdd.1))]);
                                //     gdd_desc.evaluate();
                                //     assert_eq!(new_desc, gdd_desc);
                                // }
                                // if new_desc < desc {
                                //     dbg!(format!("{}", new_desc));
                                // }
                                to_visit.push(Reverse(new_desc));
                                generated += 1;
                                progress!(format!(
                                    " ❌{:>2}/{:>2} 📃{:<6} {} 💥{}",
                                    desc.number_of_targets(),
                                    best,
                                    visited.len(),
                                    fmt(&desc.target_vector),
                                    generated
                                ));
                            } else {
                                // dbg!(fmt(&new_desc.target_vector));
                            }
                        }
                    }
                }
            }
            visited.insert(desc);
        }
        println!();
        dbg!(generated);
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
