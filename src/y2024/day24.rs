//! <https://adventofcode.com/2024/day/24>
#![allow(clippy::type_complexity)]
use {
    crate::framework::{aoc_at, AdventOfCode, ParseError},
    itertools::Itertools,
    petgraph::{
        dot::{Config, Dot},
        Graph,
    },
    // rayon::prelude::*,
    rustc_data_structures::fx::{FxHashMap, FxHashSet, FxHasher},
    serde::Serialize,
    std::{
        collections::{HashMap, HashSet},
        hash::BuildHasherDefault,
        sync::OnceLock,
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
type WireRef = &'static Wire;
type GateSpec = (WireRef, (Gate, WireRef, WireRef));
type WireMap<T> = FxHashMap<WireRef, T>;
type WireTree = FxHashMap<WireRef, FxHashSet<WireRef>>;

/// convert from 'ord', 0 to 45, to wire
fn ord_to_wire(n: usize, prefix: u8) -> WireRef {
    WIRE_NAMES
        .get()
        .unwrap()
        .get(&(prefix, b'0' + ((n / 10) as u8), b'0' + ((n % 10) as u8)))
        .unwrap()
}

/// convert  `Wire` to its string representation
fn wire_to_string((a, b, c): &Wire) -> String {
    format!("{}{}{}", *a as char, *b as char, *c as char)
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
enum Role {
    Input(usize),
    Stage1Xor(usize),
    Output(usize),
    Stage1And(usize),
    Stage2And(usize),
    Carry(usize),
}

// `?` returns if the value is `None`, so we can't use `Option<WireRef>` in checking.
type ConnectionError = FxHashSet<WireRef>;

fn merge_wires(set1: ConnectionError, set2: ConnectionError) -> ConnectionError {
    set1.union(&set2).cloned().collect()
}

#[derive(Clone, Debug, Default, Eq, PartialEq, Serialize)]
pub struct FullAdder {
    input_bits: usize,
    dep_graph: WireMap<(Gate, WireRef, WireRef)>,
}

impl FullAdder {
    fn new(input_bits: usize, overrides: &[(GateSpec, GateSpec)]) -> FullAdder {
        let mut dep_graph: WireMap<(Gate, WireRef, WireRef)> =
            PROPAGATION_TABLE.get().unwrap().clone();
        for ((g1_out, g1), (g2_out, g2)) in overrides.iter() {
            dep_graph.insert(*g1_out, *g2);
            dep_graph.insert(*g2_out, *g1);
        }
        FullAdder {
            input_bits,
            dep_graph,
        }
    }
    fn add(&self, arg1: usize, arg2: usize) -> (usize, Vec<bool>) {
        let input_bits = *INPUT_BITS.get().unwrap();
        let bit1 = int_to_bit_vector(arg1, input_bits);
        let bit2 = int_to_bit_vector(arg2, input_bits);
        let mut values: WireMap<Option<bool>> =
            HashMap::<_, _, BuildHasherDefault<FxHasher>>::default();

        for i in 0..input_bits {
            let wire1 = ord_to_wire(i, b'x');
            values.insert(wire1, Some(bit1.get(i) == Some(&true)));
            let wire2 = ord_to_wire(i, b'y');
            values.insert(wire2, Some(bit2.get(i) == Some(&true)));
        }
        fn gate_output(
            dep_graph: &WireMap<(Gate, WireRef, WireRef)>,
            values: &mut WireMap<Option<bool>>,
            wire: WireRef,
        ) -> Option<bool> {
            if let Some(b) = values.get(wire) {
                return b.map(|b| b);
            }
            let (g, w1, w2) = dep_graph.get(wire)?;
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
        let v = (0..=input_bits)
            .map(|i| {
                gate_output(&self.dep_graph, &mut values, ord_to_wire(i, b'z')).is_some_and(|b| b)
            })
            .collect::<Vec<_>>();
        let val = v
            .iter()
            .rev()
            .fold(0_usize, |acc, b| acc * 2 + (*b as usize));
        (val, v)
    }
    // XOR -> XOR -> z(n)
    // AND -> OR -> non-z
    // XOR -> AND -> OR -> XOR -> z(n+1)
    // XOR -> AND -> OR -> { AND -> OR }+ -> z(*)
    fn check_flows_to_z(&self, tree: &WireTree, i: usize, prefix: u8) -> ConnectionError {
        if i == 0 {
            return HashSet::<WireRef, BuildHasherDefault<FxHasher>>::default();
        }
        self.check_flow(tree, ord_to_wire(i, prefix), Role::Input(i))
    }
    fn check_flow(&self, tree: &WireTree, from: WireRef, role: Role) -> ConnectionError {
        let subs = if let Some(subs) = tree.get(from) {
            subs.iter()
                .map(|g| (*g, self.dep_graph.get(g).unwrap().0))
                .collect::<Vec<_>>()
        } else {
            vec![]
        };
        // dbg!(subs.iter().map(|g| wire_to_string(g)).collect::<Vec<_>>());
        let mut invalid = HashSet::<WireRef, BuildHasherDefault<FxHasher>>::default();
        invalid.insert(from);
        match role {
            Role::Input(n) => {
                if subs.len() != 2 {
                    return invalid;
                }
                match (subs[0].1, subs[1].1) {
                    (Gate::Xor, Gate::And) => merge_wires(
                        self.check_flow(tree, subs[0].0, Role::Stage1Xor(n)),
                        self.check_flow(tree, subs[1].0, Role::Stage1And(n)),
                    ),
                    (Gate::And, Gate::Xor) => merge_wires(
                        self.check_flow(tree, subs[0].0, Role::Stage1And(n)),
                        self.check_flow(tree, subs[1].0, Role::Stage1Xor(n)),
                    ),
                    _ => invalid,
                }
            }
            Role::Output(n) => {
                if subs.len() == 0 && from == ord_to_wire(n, b'z') {
                    HashSet::<WireRef, BuildHasherDefault<FxHasher>>::default()
                } else {
                    invalid
                }
            }
            Role::Stage1And(n) => {
                if subs.len() != 1 {
                    return invalid;
                }
                self.check_flow(tree, subs[0].0, Role::Carry(n))
            }
            Role::Stage2And(n) => {
                if subs.len() != 1 {
                    return invalid;
                }
                self.check_flow(tree, subs[0].0, Role::Carry(n))
            }
            Role::Carry(n) if n == self.input_bits - 1 => {
                if subs.len() == 0 && from == ord_to_wire(n + 1, b'z') {
                    HashSet::<WireRef, BuildHasherDefault<FxHasher>>::default()
                } else {
                    invalid
                }
            }
            Role::Carry(n) => {
                if subs.len() != 2 {
                    return invalid;
                }
                match (subs[0].1, subs[1].1) {
                    (Gate::Xor, Gate::And) => self.check_flow(tree, subs[0].0, Role::Output(n + 1)),
                    (Gate::And, Gate::Xor) => self.check_flow(tree, subs[1].0, Role::Output(n + 1)),
                    _ => invalid,
                }
            }
            Role::Stage1Xor(n) => {
                if subs.len() != 2 {
                    return invalid;
                }
                match (subs[0].1, subs[1].1) {
                    (Gate::Xor, Gate::And) => merge_wires(
                        self.check_flow(tree, subs[0].0, Role::Output(n)),
                        self.check_flow(tree, subs[1].0, Role::Stage2And(n)),
                    ),
                    (Gate::And, Gate::Xor) => merge_wires(
                        self.check_flow(tree, subs[0].0, Role::Stage2And(n)),
                        self.check_flow(tree, subs[1].0, Role::Output(n)),
                    ),
                    _ => invalid,
                }
            }
        }
    }
}

#[derive(Clone, Debug, Default, Eq, Hash, PartialEq, Serialize)]
pub struct Descriptor {
    input_bits: usize,
    target_vector: Vec<bool>,
    overrides: Vec<(GateSpec, GateSpec)>,
}

/* impl Ord for Descriptor {
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
} */

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
    fn new(input_bits: usize, overrides: Vec<(GateSpec, GateSpec)>) -> Descriptor {
        Descriptor {
            input_bits,
            target_vector: Vec::new(),
            overrides,
        }
    }
    // fn evaluate(&mut self) {
    //     self.target_vector = self
    //         .check_correctness()
    //         .iter()
    //         .zip(self.check_structure().iter())
    //         .map(|(a, b)| *a | *b)
    //         .collect();
    // }
    fn add_swaps(&self, w1: WireRef, w2: WireRef) -> Option<Descriptor> {
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
        Some(Descriptor::new(self.input_bits, swaps))
    }
    fn build_adder(&self) -> FullAdder {
        FullAdder::new(self.input_bits, &self.overrides)
    }
    /// return `(down_tree, up_tree)`
    fn wire_trees(&self, down: bool, up: bool) -> (WireTree, WireTree) {
        let adder = self.build_adder();
        let mut wires: FxHashSet<WireRef> =
            HashSet::<WireRef, BuildHasherDefault<FxHasher>>::default();
        let mut down_tree: FxHashMap<WireRef, FxHashSet<WireRef>> =
            HashMap::<_, _, BuildHasherDefault<FxHasher>>::default();
        let mut up_tree: FxHashMap<WireRef, FxHashSet<WireRef>> =
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
static PROPAGATION_TABLE: OnceLock<WireMap<(Gate, WireRef, WireRef)>> = OnceLock::new();

fn build_swapped_pair((pick1, pick2): (WireRef, WireRef)) -> (GateSpec, GateSpec) {
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
    )
}

#[derive(Clone, Debug, Default, Eq, PartialEq, Serialize)]
pub struct Puzzle {
    input_wire: Vec<(Wire, bool)>,
}

mod parser {
    use {
        super::{Gate, Wire},
        crate::parser::parse_usize,
        winnow::{
            ascii::newline,
            combinator::{alt, separated, seq},
            token::one_of,
            PResult, Parser,
        },
    };

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

    pub fn parse(s: &mut &str) -> PResult<(Vec<(Wire, bool)>, Vec<(Gate, Wire, Wire, Wire)>)> {
        seq!(
            separated(1.., parse_setting, newline),
            _: (newline, newline),
            separated(1.., parse_connection, newline)
        )
        .parse_next(s)
    }
}

#[aoc_at(2024, 24)]
impl AdventOfCode for Puzzle {
    type Output1 = usize;
    type Output2 = String;
    fn parse(&mut self, input: String) -> Result<String, ParseError> {
        let (wires, links) = parser::parse(&mut input.as_str())?;
        self.input_wire = wires;
        let mut wire_names_tmp: FxHashSet<Wire> =
            HashSet::<_, BuildHasherDefault<FxHasher>>::default();
        for (_, i1, i2, o) in links.iter() {
            wire_names_tmp.insert(*i1);
            wire_names_tmp.insert(*i2);
            wire_names_tmp.insert(*o);
        }
        if WIRE_NAMES.get().is_none() {
            WIRE_NAMES.set(wire_names_tmp).unwrap();
        }
        let wire_names: &'static FxHashSet<Wire> = WIRE_NAMES.get().unwrap();
        let mut propagation_table: WireMap<(Gate, WireRef, WireRef)> = FxHashMap::default();
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
        // firstly, write a dot file
        let weight = "".to_string();
        let mut graph_id: HashMap<&String, _> = HashMap::new();
        let mut graph = Graph::<&String, &String>::new();
        for (node, inputs) in data.iter() {
            let to = if graph_id.contains_key(&node) {
                *graph_id.get(node).unwrap()
            } else {
                graph.add_node(node)
            };
            graph_id.insert(node, to);
            for input in inputs.iter() {
                let from =
                    if let std::collections::hash_map::Entry::Vacant(e) = graph_id.entry(input) {
                        let from = graph.add_node(input);
                        e.insert(from);
                        from
                    } else {
                        *graph_id.get(input).unwrap()
                    };
                graph.add_edge(from, to, &weight);
            }
        }
        self.dump_to(
            "nodes.dot",
            format!("{:?}", Dot::with_config(&graph, &[Config::EdgeNoLabel])),
        );
        serde_json::to_string(&data).ok()
    }
    fn part1(&mut self) -> Self::Output1 {
        let input_bits = *INPUT_BITS.get().unwrap();
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
        FullAdder::new(input_bits, &Vec::new()).add(x, y).0
    }
    fn part2(&mut self) -> Self::Output2 {
        let input_bits = *INPUT_BITS.get().unwrap();
        let config = Descriptor::new(input_bits, vec![]);
        let circuit = config.build_adder();
        let mut checker = config.clone();
        let (d_tree, _) = config.wire_trees(true, false);
        let mut result: FxHashSet<WireRef> = HashSet::<_, BuildHasherDefault<FxHasher>>::default();
        let mut buffer: FxHashSet<WireRef> = HashSet::<_, BuildHasherDefault<FxHasher>>::default();
        for i in 1..input_bits {
            let pair = merge_wires(
                circuit.check_flows_to_z(&d_tree, i, b'x'),
                circuit.check_flows_to_z(&d_tree, i, b'y'),
            );
            buffer = merge_wires(buffer, pair.clone());
            if 2 <= buffer.len() {
                let l = buffer.iter().cloned().collect::<Vec<_>>();
                assert_eq!(l.len(), 2);
                checker = checker.add_swaps(l[0], l[1]).unwrap();
                buffer.clear();
            }
            result = merge_wires(result, circuit.check_flows_to_z(&d_tree, i, b'x'));
            result = merge_wires(result, circuit.check_flows_to_z(&d_tree, i, b'y'));
        }
        // check the result
        let (d_tree, _) = checker.wire_trees(true, false);
        let adder = checker.build_adder();
        for i in 1..input_bits {
            assert!(adder.check_flows_to_z(&d_tree, i, b'x').is_empty());
            assert!(adder.check_flows_to_z(&d_tree, i, b'y').is_empty());
        }
        result
            .iter()
            .cloned()
            .map(wire_to_string)
            .sorted()
            .join(",")
    }
}
