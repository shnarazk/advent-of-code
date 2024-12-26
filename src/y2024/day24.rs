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
    rustc_data_structures::fx::{FxHashMap, FxHasher},
    serde::{Deserialize, Serialize},
    std::{
        collections::{HashMap, HashSet},
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

const PERSISTENT_STORAGE: &'static str = "misc/2024/day23-diff-table.json";

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
    overrides: Vec<(GateSpec, GateSpec)>,
}

impl Adder {
    fn new(overrides: Vec<(GateSpec, GateSpec)>) -> Adder {
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
            for gates in self.overrides.iter() {
                if self.evaluate(&mut values, &gates.0).is_some() {
                    propagated = true;
                    continue;
                }
                if self.evaluate(&mut values, &gates.1).is_some() {
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
    fn affect_bits(&self, final_check: bool) -> Vec<bool> {
        let base = BASE_OUTPUT.get().unwrap();
        let input_bits = *INPUT_BITS.get().unwrap();
        let ret = (0..input_bits)
            .collect::<Vec<_>>()
            .par_iter()
            .map(|bit1| {
                let target_value1 = 1_usize << *bit1;
                (bit1 + 1..input_bits)
                    .map(|bit2| {
                        let target_value2 = 1_usize << bit2;
                        let x = target_value1;
                        let y = target_value2;
                        let base = if final_check {
                            x + y
                        } else {
                            *base.get(&(x, y)).unwrap()
                        };
                        let v = self.add(x, y).1;
                        (0..input_bits + 1)
                            .map(|index| {
                                v.get(index)
                                    .map_or(true, |b| *b != (0 != base & (1 << index)))
                            })
                            .collect::<Vec<_>>()
                    })
                    .map(|f| f)
                    .fold(vec![false; input_bits + 1], |mut acc, v| {
                        for (i, p) in acc.iter_mut().enumerate() {
                            *p |= v[i];
                        }
                        acc
                    })
            })
            .collect::<Vec<_>>()
            .iter()
            .fold(vec![false; input_bits + 1], |mut acc, v| {
                for (i, p) in acc.iter_mut().enumerate() {
                    *p |= v[i];
                }
                acc
            });
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
    fn all_outputs(&self) -> HashMap<(usize, usize), usize> {
        let mut hash: HashMap<(usize, usize), usize> = HashMap::new();
        let input_bits = *INPUT_BITS.get().unwrap();
        (0..input_bits).for_each(|bit1| {
            let target_value1 = 1_usize << bit1;
            (bit1 + 1..input_bits).for_each(|bit2| {
                let target_value2 = 1_usize << bit2;
                let x = target_value1;
                let y = target_value2;
                hash.insert((x, y), self.add(x, y).0);
            })
        });
        hash
    }
    /// return `(down_tree, up_tree)`
    fn wire_trees(&self) -> (HashMap<Wire, HashSet<Wire>>, HashMap<Wire, HashSet<Wire>>) {
        let base_links = BASE_LINK.get().unwrap();
        let mut wires: HashSet<Wire> = HashSet::new();
        let mut down_tree: HashMap<Wire, HashSet<Wire>> = HashMap::new();
        let mut up_tree: HashMap<Wire, HashSet<Wire>> = HashMap::new();
        for entry in base_links.iter() {
            let (g, i1, i2, o) =
                if let Some(ps) = self.overrides.iter().find(|(g, _)| entry.3 == g.3) {
                    (entry.0, entry.1, entry.2, ps.1 .3)
                } else if let Some(ps) = self.overrides.iter().find(|(_, g)| entry.3 == g.3) {
                    (entry.0, entry.1, entry.2, ps.0 .3)
                } else {
                    *entry
                };
            wires.insert(i1);
            wires.insert(i2);
            wires.insert(o);
            down_tree.entry(i1).or_default().insert(o);
            down_tree.entry(i2).or_default().insert(o);
            up_tree.entry(o).or_default().insert(i1);
            up_tree.entry(o).or_default().insert(i2);
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
                        ['x', 'y', 'z'].contains(&w.0),
                        "unlinked wire: {} from {}",
                        wire_name(&w),
                        wire_name(&wire),
                    );
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
static BASE_OUTPUT: OnceLock<HashMap<(usize, usize), usize>> = OnceLock::new();
static DIFF_MAP: OnceLock<HashMap<(Wire, Wire), Vec<usize>>> = OnceLock::new();

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
    fn build_search_table(&mut self) {
        #[derive(Debug, Default, Eq, PartialEq, Deserialize, Serialize)]
        struct Record {
            key: (String, String),
            value: Vec<usize>,
        }
        let path = std::path::Path::new(PERSISTENT_STORAGE);
        if path.exists() {
            match File::open(&path) {
                Ok(mut file) => {
                    let mut contents = String::new();
                    file.read_to_string(&mut contents).expect("read error");
                    let Ok(vec) = serde_json::from_str::<Vec<Record>>(&contents) else {
                        panic!("Can't read {PERSISTENT_STORAGE}");
                    };
                    println!(
                        "{}# read intermediate data on {}{}",
                        color::MAGENTA,
                        PERSISTENT_STORAGE,
                        color::RESET,
                    );
                    if DIFF_MAP.get().is_none() {
                        let hash = vec
                            .iter()
                            .map(|r| {
                                let w1 = r.key.0.chars().collect::<Vec<char>>();
                                let w2 = r.key.1.chars().collect::<Vec<char>>();
                                let v = r.value.iter().map(|n| *n).collect::<Vec<usize>>();
                                (((w1[0], w1[1], w1[2]), (w2[0], w2[1], w2[2])), v)
                            })
                            .filter(|((w1, w2), _)| {
                                assert!(w1 < w2);
                                true
                            })
                            .collect::<HashMap<(Wire, Wire), Vec<usize>>>();
                        DIFF_MAP.set(hash).unwrap();
                    }
                }
                Err(e) => panic!("Can't read {PERSISTENT_STORAGE}: {e:?}"),
            }
            return;
        }
        println!("{}# build diff table{}", color::MAGENTA, color::RESET,);
        let mut memo: HashMap<(Wire, Wire), Vec<usize>> = HashMap::new();
        let input_bits = *INPUT_BITS.get().unwrap();
        let relevants = WIRE_NAMES
            .get()
            .unwrap()
            .iter()
            .filter(|wire| wire.0 != 'x' && wire.0 != 'y')
            .sorted()
            .collect::<Vec<_>>();
        let mut to_search: Vec<(Wire, Wire)> = vec![];
        let num_lifts: usize = 0;
        let adder = Adder::new(Vec::new());
        let wrong_vector = adder.wrong_bits();
        let num_wrong_bits = wrong_vector.iter().filter(|b| **b).count();
        dbg!(relevants.len());
        let (down_tree, up_tree) = adder.wire_trees();
        for (i, pick1) in relevants.iter().enumerate() {
            for pick2 in relevants.iter().skip(i + 1) {
                to_search.push((**pick1, **pick2));
            }
        }
        for (i, case) in to_search.iter().enumerate() {
            progress!(format!(
                "{i:>6}/{:>6} :: {}-{}",
                to_search.len(),
                wire_name(&case.0),
                wire_name(&case.1)
            ));
            let gates = build_swapped_pair(case);
            let sw = vec![gates];
            let result_vector = Adder::new(sw.clone()).affect_bits(false);
            memo.insert(
                (case.0, case.1),
                result_vector
                    .iter()
                    .map(|b| *b as usize)
                    .collect::<Vec<_>>(),
            );
        }

        let vec = memo
            .iter()
            .map(|(k, v)| Record {
                key: (wire_name(&k.0), wire_name(&k.1)),
                value: v.iter().map(|b| *b as usize).collect::<Vec<_>>(),
            })
            .collect::<Vec<_>>();
        if let Some(json) = serde_json::to_string(&vec).ok() {
            let dir = std::path::Path::new(PERSISTENT_STORAGE).parent().unwrap();
            if !dir.exists() {
                std::fs::create_dir_all(dir)
                    .unwrap_or_else(|_| panic!("fail to create a directory {dir:?}"));
            }
            let mut file = File::create(PERSISTENT_STORAGE)
                .unwrap_or_else(|_| panic!("fail to open {PERSISTENT_STORAGE}"));
            writeln!(file, "{}", json).expect("fail to save");
            println!(
                "{}# write JSON data on {}{}",
                color::MAGENTA,
                PERSISTENT_STORAGE,
                color::RESET,
            );
        }
        if DIFF_MAP.get().is_none() {
            DIFF_MAP.set(memo).unwrap();
        }
    }
    fn search(
        &self,
        level: usize,
        swaps: Vec<(GateSpec, GateSpec)>,
        diff_vector: Vec<usize>,
        // memo: &mut HashMap<Vec<(GateSpec, GateSpec)>, usize>,
    ) -> Option<Vec<(GateSpec, GateSpec)>> {
        if level == 2 {
            let diff_vectors: Vec<(Wire, Wire)> = DIFF_MAP
                .get()
                .unwrap()
                .iter()
                .filter(|(_, v)| **v == diff_vector)
                .map(|(k, v)| *k)
                .sorted()
                .collect::<Vec<_>>();
            let mut tries = Vec::new();
            for (i, swap1) in diff_vectors.iter().enumerate() {
                for swap2 in diff_vectors.iter().skip(i + 1) {
                    tries.push((swap1, swap2));
                }
            }
            for (i, (swap1, swap2)) in tries.iter().enumerate() {
                let mut sw = swaps.clone();
                sw.push(build_swapped_pair(swap1));
                sw.push(build_swapped_pair(swap2));

                progress!(format!(
                    " => ({i:>5}/{:>5}) :: {}-{}-{}-{}",
                    tries.len(),
                    wire_name(&swap1.0),
                    wire_name(&swap1.1),
                    wire_name(&swap2.0),
                    wire_name(&swap2.1),
                ));
                let result_vector = Adder::new(sw.clone()).affect_bits(true);
                if result_vector.iter().all(|b| !*b) {
                    dbg!(sw);
                    panic!();
                }
            }
            return None;
        }
        let input_bits = *INPUT_BITS.get().unwrap();
        let diff_vectors: &HashMap<(Wire, Wire), Vec<usize>> = DIFF_MAP.get().unwrap();
        let relevants = WIRE_NAMES
            .get()
            .unwrap()
            .iter()
            .filter(|wire| wire.0 != 'x' && wire.0 != 'y')
            .filter(|wire| {
                swaps
                    .iter()
                    .all(|(gs1, gs2)| gs1.3 != **wire && gs2.3 != **wire)
            })
            .sorted()
            .collect::<Vec<_>>();
        let mut to_search: Vec<(Wire, Wire)> = vec![];
        let adder = Adder::new(swaps.clone());
        // let wrong_vector = adder.wrong_bits();
        // let num_wrong_bits = wrong_vector.iter().filter(|b| **b).count();
        let (down_tree, up_tree) = adder.wire_trees();
        if false && level == 1 {
            let (down_tree, up_tree) = adder.wire_trees();
            for (i, pick1) in relevants.iter().enumerate() {
                let pick1_cond = adder
                    .wire_affects(&down_tree, **pick1)
                    .contains(&bit_to_wire(5, 'z'));
                for pick2 in relevants.iter() {
                    let pick2_cond = adder
                        .wire_affects(&up_tree, **pick2)
                        .iter()
                        .any(|w| *w == bit_to_wire(5, 'x') || *w == bit_to_wire(5, 'y'));
                    if pick1_cond && pick2_cond && pick1 != pick2 {
                        if pick1 < pick2 {
                            to_search.push((**pick1, **pick2));
                        } else {
                            to_search.push((**pick2, **pick1));
                        }
                    }
                }
            }
        } else if false && level == 2 {
            let (down_tree, up_tree) = adder.wire_trees();
            for (i, pick1) in relevants.iter().enumerate() {
                let pick1_cond = adder
                    .wire_affects(&down_tree, **pick1)
                    .contains(&bit_to_wire(20, 'z'));
                for pick2 in relevants.iter() {
                    let pick2_cond = adder
                        .wire_affects(&up_tree, **pick2)
                        .iter()
                        .any(|w| *w == bit_to_wire(20, 'x') || *w == bit_to_wire(20, 'y'));
                    if pick1_cond && pick2_cond && pick1 != pick2 {
                        if pick1 < pick2 {
                            to_search.push((**pick1, **pick2));
                        } else {
                            to_search.push((**pick2, **pick1));
                        }
                    }
                }
            }
        } else {
            for (i, pick1) in relevants.iter().enumerate() {
                for pick2 in relevants.iter().skip(i + 1) {
                    to_search.push((**pick1, **pick2));
                }
            }
        }
        let mut a = (0, 0, 0);
        for (i, case) in to_search.iter().enumerate() {
            // println!("{}-{}", wire_name(pick1), wire_name(pick2));
            if 0 < level {
                progress!(format!(
                    "level:{level:>2}({i:>5}/{:>5}) :: {}-{}",
                    to_search.len(),
                    wire_name(&case.0),
                    wire_name(&case.1)
                ));
            }
            let mut sw = swaps.clone();
            let vec = diff_vectors
                .get(case)
                .expect(format!("{case:?}").as_str())
                .clone()
                .iter()
                .enumerate()
                .map(|(i, a)| *a + diff_vector[i])
                .collect::<Vec<_>>();
            sw.push(build_swapped_pair(case));
            assert!(sw.len() <= 4);
            let result_vector = Adder::new(sw.clone()).affect_bits(true);
            let num_vector = result_vector
                .iter()
                .map(|b| *b as usize)
                .collect::<Vec<_>>();
            let merged = result_vector
                .iter()
                .enumerate()
                .map(|(i, b)| *b as usize + diff_vector[i])
                .collect::<Vec<_>>();
            let affects = result_vector.iter().filter(|b| **b).count();
            if affects < level {
                if level == 4 && !result_vector[9] {
                    println!("{i:>5}:{}", fmt(&result_vector));
                    if let Some(ret) = self.search(
                        level - 1,
                        sw,
                        result_vector
                            .iter()
                            .map(|b| *b as usize)
                            .collect::<Vec<_>>(),
                    ) {}
                } else if level == 3 && !result_vector[37] {
                    println!("{i:>5}:{}", fmt(&result_vector));
                    if let Some(ret) = self.search(
                        level - 1,
                        sw,
                        result_vector
                            .iter()
                            .map(|b| *b as usize)
                            .collect::<Vec<_>>(),
                    ) {}
                } else if level == 2 && !result_vector[20] {
                    println!("{i:>5}:{}", fmt(&result_vector));
                    if let Some(ret) = self.search(
                        level - 1,
                        sw,
                        result_vector
                            .iter()
                            .map(|b| *b as usize)
                            .collect::<Vec<_>>(),
                    ) {}
                }
                a.2 += 1;
            } else if level == 2 && diff_vector == num_vector {
                // println!("{i:>5}:{}", fmt(&result_ector));
                if let Some(ret) = self.search(
                    level - 1,
                    sw,
                    result_vector
                        .iter()
                        .map(|b| *b as usize)
                        .collect::<Vec<_>>(),
                ) {}
                a.1 += 1;
            } else if level == 1 && affects == 0 {
                println!("{i:>5}:{}", fmt(&result_vector));
                panic!();
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
        let adder = Adder::new(Vec::new());
        if BASE_OUTPUT.get().is_none() {
            let hash = adder.all_outputs();
            let input_bits = *INPUT_BITS.get().unwrap();
            assert_eq!(hash.len(), input_bits * (input_bits - 1) / 2);
            BASE_OUTPUT.set(hash).unwrap();
        }
        self.build_search_table();
        let init_vector = adder
            .affect_bits(true)
            .iter()
            .map(|b| *b as usize)
            .collect::<Vec<_>>();
        dbg!(fmt_(&init_vector));
        if let Some(vec) = self.search(4, Vec::new(), init_vector) {
            vec.iter()
                .flat_map(|(gs1, gs2)| vec![wire_name(&gs1.3), wire_name(&gs2.3)])
                .sorted()
                .join(",")
        } else {
            "".to_string()
        }
    }
}
