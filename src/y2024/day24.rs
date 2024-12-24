//! <https://adventofcode.com/2024/day/24>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{aoc_at, AdventOfCode, ParseError},
        geometric::neighbors,
        parser::parse_usize,
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
        ops::Bound,
        panic::resume_unwind,
    },
    winnow::{
        ascii::newline,
        combinator::{alt, repeat, repeat_till, separated, seq, terminated},
        token::one_of,
        PResult, Parser,
    },
};

type Wire = (char, char, char);

fn bit_to_wire(n: usize, prefix: char) -> Wire {
    (
        prefix,
        (b'0' + ((n / 10) as u8)) as char,
        (b'0' + ((n % 10) as u8)) as char,
    )
}

fn wire_to_ord((_, b, c): &(char, char, char)) -> usize {
    (((*b as u8) - b' ') as usize) * 10 + (((*c as u8) - b' ') as usize)
}

fn wire_name((a, b, c): &(char, char, char)) -> String {
    format!("{a}{b}{c}")
}

#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
enum Gate {
    #[default]
    And,
    Or,
    Xor,
}

#[derive(Clone, Debug, Default, Eq, PartialEq, Serialize)]
pub struct Puzzle {
    wire: Vec<(Wire, bool)>,
    link: Vec<(Gate, Wire, Wire, Wire)>,
    value: FxHashMap<Wire, bool>,
    wire_downward: HashMap<Wire, HashSet<Wire>>,
    wire_upward: HashMap<Wire, HashSet<Wire>>,
    input_bits: usize,
}

impl Puzzle {
    fn seek(&self, wrong_bits: &[usize], founds: Vec<Wire>) -> Option<(Puzzle, Vec<Wire>)> {
        if let Some(&wrong_bit) = wrong_bits.first() {
            let t1 = self.wire_tree_downward(bit_to_wire(wrong_bit, 'x'));
            let t2 = self.wire_tree_downward(bit_to_wire(wrong_bit, 'y'));
            let to = self.wire_tree_upward(bit_to_wire(wrong_bit, 'z'));
            let relevants1 = to
                .union(&t1)
                .filter(|n| n.0 != 'x' && n.0 != 'y')
                .cloned()
                .collect::<HashSet<_>>();
            let relevants2 = to
                .union(&t2)
                .filter(|n| n.0 != 'x' && n.0 != 'y')
                .cloned()
                .collect::<HashSet<_>>();
            let relevants = relevants1
                .union(&relevants2)
                .cloned()
                .sorted()
                .collect::<Vec<_>>();
            // println!("{} :: |set|:{}", wrong_bit, relevants.len());

            for (i, pick1) in relevants.iter().enumerate() {
                'fail: for pick2 in relevants.iter().skip(i + 1) {
                    // println!("{}-{}", wire_name(pick1), wire_name(pick2));
                    for setting in
                        [(false, false), (false, true), (true, false), (true, true)].iter()
                    {
                        let mut checker = self.new_swapped(pick1, pick2);
                        checker.value.insert(bit_to_wire(wrong_bit, 'x'), setting.0);
                        checker.value.insert(bit_to_wire(wrong_bit, 'y'), setting.1);
                        let (val, v) = checker.eval();

                        // println!(
                        //     "  {}{}{}{}: {:?} = {}",
                        //     (setting.0 as usize),
                        //     (setting.1 as usize),
                        //     (setting.2 as usize),
                        //     (setting.3 as usize),
                        //     v.iter().rev().map(|b| *b as usize).collect::<Vec<_>>(),
                        //     val,
                        // );
                        let x = (1_usize << wrong_bit) * (setting.0 as usize);
                        let y = (1_usize << wrong_bit) * (setting.1 as usize);
                        if x + y != val {
                            continue 'fail;
                        }
                    }

                    let affected1 = self.wire_tree_upward(*pick1);
                    let aff1 = affected1
                        .iter()
                        .filter(|n| n.0 == 'x' || n.0 == 'y')
                        .cloned()
                        .collect::<HashSet<_>>();
                    let affected2 = self.wire_tree_upward(*pick2);
                    let aff2 = affected2
                        .iter()
                        .filter(|n| n.0 == 'x' || n.0 == 'y')
                        .cloned()
                        .collect::<HashSet<_>>();
                    let aff = aff1.union(&aff2).cloned().collect::<HashSet<_>>();
                    let aff_x = aff1
                        .iter()
                        .filter(|n| n.0 == 'x')
                        .sorted()
                        .cloned()
                        .collect::<Vec<_>>();

                    let aff_y = aff2
                        .iter()
                        .filter(|n| n.0 == 'x')
                        .sorted()
                        .cloned()
                        .collect::<Vec<_>>();

                    let checker = self.new_swapped(pick1, pick2);
                    let passed = checker.check_exhausitively(wrong_bit + 1);
                    if passed {
                        println!(
                            "attemp({:>2}): {}-{}: {}, affecting {:?} + {:?}",
                            wrong_bit,
                            wire_name(pick1),
                            wire_name(pick2),
                            passed,
                            aff_x.iter().map(|n| wire_to_ord(n)).collect::<Vec<_>>(),
                            aff_y.iter().map(|n| wire_to_ord(n)).collect::<Vec<_>>(),
                        );
                        let mut f = founds.clone();
                        f.push(*pick1);
                        f.push(*pick2);
                        // if let Some(s) = checker.seek(&wrong_bits[1..], f) {
                        //     return Some(s);
                        // }
                        checker.seek(&wrong_bits[1..], f);
                    }
                }
            }
            None
        } else {
            println!(
                "{:?}",
                founds
                    .iter()
                    .map(|t| format!("{}{}{}", t.0, t.1, t.2))
                    .join(",")
            );
            Some((self.clone(), founds))
        }
    }
    /// return a clean cloned itself
    fn new(&self) -> Puzzle {
        let mut checker = self.clone();
        for (name, b) in checker.value.iter_mut() {
            *b = false;
        }
        checker
    }
    fn new_swapped(&self, pick1: &Wire, pick2: &Wire) -> Puzzle {
        let mut checker = self.new();
        for gate in checker.link.iter_mut() {
            if gate.3 == *pick1 {
                gate.3 = *pick2;
            } else if gate.3 == *pick2 {
                gate.3 = *pick1;
            }
        }
        checker
    }
    /// exhaustive-check
    fn check_exhausitively(&self, range: usize) -> bool {
        let band = 1_usize << range;
        for target_input1 in 0..self.input_bits {
            let target_value1 = 1_usize << target_input1;
            for target_input2 in (target_input1 + 1)..self.input_bits {
                let target_value2 = 1_usize << target_input2;
                let mut checker = self.new();
                checker.value.insert(bit_to_wire(target_input1, 'x'), true);
                checker.value.insert(bit_to_wire(target_input2, 'y'), true);

                let (n, v) = checker.eval();
                if (target_value1 + target_value2) % band != n % band {
                    println!(
                        "failed 0..{}: {}, {}: {:?}",
                        range,
                        target_input1,
                        target_input2,
                        v.iter().rev().map(|b| *b as usize).collect::<Vec<_>>(),
                    );
                    return false;
                }
                assert_eq!(v.len(), self.input_bits + 1);
            }
        }
        true
    }
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
    fn wire_tree_downward(&self, wire: Wire) -> HashSet<Wire> {
        let mut to_visit: Vec<Wire> = self
            .wire_downward
            .get(&wire)
            .unwrap()
            .iter()
            .cloned()
            .collect::<Vec<_>>();
        let mut result: HashSet<Wire> = HashSet::new();
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
        result
    }
    fn wire_tree_upward(&self, wire: Wire) -> HashSet<Wire> {
        let mut to_visit: Vec<Wire> = self
            .wire_upward
            .get(&wire)
            .unwrap()
            .iter()
            .cloned()
            .collect::<Vec<_>>();
        let mut result: HashSet<Wire> = HashSet::new();
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
        self.wire = wires;
        self.link = links;
        Self::parsed()
    }
    fn end_of_data(&mut self) {
        for (w, b) in self.wire.iter() {
            self.value.insert(*w, *b);
        }
        for (g, i1, i2, o) in self.link.iter() {
            self.wire_downward.entry(*i1).or_default().insert(*o);
            self.wire_downward.entry(*i2).or_default().insert(*o);
            self.wire_upward.entry(*o).or_default().insert(*i1);
            self.wire_upward.entry(*o).or_default().insert(*i2);
        }
        self.input_bits = self.wire.iter().filter(|(g, _)| g.0 == 'x').count();
    }
    fn part1(&mut self) -> Self::Output1 {
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
        self.value
            .iter()
            .filter(|(wire, _)| wire.0 == 'z')
            .sorted()
            .rev()
            .map(|(_, b)| b)
            .fold(0_usize, |acc, b| acc * 2 + (*b as usize))
    }
    fn part2(&mut self) -> Self::Output2 {
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

        if let Some((_, vec)) = self.seek(&wrong_bits, Vec::new()) {
            vec.iter()
                .sorted()
                .map(|t| format!("{}{}{}", t.0, t.1, t.2))
                .join(",")
        } else {
            unreachable!()
        }
    }
}
