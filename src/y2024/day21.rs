//! <https://adventofcode.com/2024/day/21>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::neighbors,
        parser::parse_usize,
    },
    itertools::Itertools,
    rayon::prelude::*,
    rustc_data_structures::fx::{FxHashMap, FxHasher},
    serde::Serialize,
    serde_json::to_value,
    std::{
        cmp::{Ordering, Reverse},
        collections::{BinaryHeap, HashMap},
        hash::BuildHasherDefault,
    },
    winnow::{
        ascii::newline,
        combinator::{repeat, repeat_till, separated, seq, terminated},
        token::one_of,
        PResult, Parser,
    },
};

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
enum Kind1 {
    K0,
    K1,
    K2,
    K3,
    K4,
    K5,
    K6,
    K7,
    K8,
    K9,
    KA,
}

impl std::fmt::Display for Kind1 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Kind1::K0 => '0',
                Kind1::K1 => '1',
                Kind1::K2 => '2',
                Kind1::K3 => '3',
                Kind1::K4 => '4',
                Kind1::K5 => '5',
                Kind1::K6 => '6',
                Kind1::K7 => '7',
                Kind1::K8 => '8',
                Kind1::K9 => '9',
                Kind1::KA => 'A',
            }
        )
    }
}

impl Kind1 {
    fn iterator() -> impl Iterator<Item = Kind1> {
        [
            Kind1::K0,
            Kind1::K1,
            Kind1::K2,
            Kind1::K3,
            Kind1::K4,
            Kind1::K5,
            Kind1::K6,
            Kind1::K7,
            Kind1::K8,
            Kind1::K6,
            Kind1::K7,
            Kind1::K9,
            Kind1::KA,
        ]
        .into_iter()
    }
}

const LV1LINK: [(Kind1, Kind1); 15] = [
    (Kind1::K0, Kind1::K2),
    (Kind1::K0, Kind1::KA),
    (Kind1::K1, Kind1::K2),
    (Kind1::K1, Kind1::K4),
    (Kind1::K2, Kind1::K3),
    (Kind1::K2, Kind1::K5),
    (Kind1::K3, Kind1::K6),
    (Kind1::K3, Kind1::KA),
    (Kind1::K4, Kind1::K5),
    (Kind1::K4, Kind1::K7),
    (Kind1::K5, Kind1::K6),
    (Kind1::K5, Kind1::K8),
    (Kind1::K6, Kind1::K9),
    (Kind1::K7, Kind1::K8),
    (Kind1::K8, Kind1::K9),
];

fn lv1_build_pathes(from: Kind1, to: Kind1) -> Vec<Vec<Kind1>> {
    if from == to {
        return vec![vec![to]];
    }
    let mut to_visit: Vec<Vec<Kind1>> = Vec::new();
    let mut pathes: Vec<Vec<Kind1>> = Vec::new();
    to_visit.push(vec![from]);
    while let Some(path) = to_visit.pop() {
        if path.last().unwrap() == &to {
            // path.remove(0);
            pathes.push(path);
            continue;
        }
        for (p, q) in LV1LINK.iter() {
            let r = if path.last().unwrap() == p && !path.contains(q) {
                q
            } else if path.last().unwrap() == q && !path.contains(p) {
                p
            } else {
                continue;
            };
            let mut path1 = path.clone();
            path1.push(*r);
            to_visit.push(path1);
        }
    }
    pathes.sort_unstable_by_key(|l| l.len());
    pathes
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
enum Kind2 {
    U,
    D,
    L,
    R,
    A,
}

impl std::fmt::Display for Kind2 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Kind2::U => '^',
                Kind2::D => 'v',
                Kind2::L => '<',
                Kind2::R => '>',
                Kind2::A => 'A',
            }
        )
    }
}

fn to_string(v: &[Kind2]) -> String {
    v.iter().map(|k| format!("{k}")).collect::<String>()
}

impl Kind2 {
    fn iterator() -> impl Iterator<Item = Kind2> {
        [Kind2::U, Kind2::D, Kind2::L, Kind2::R, Kind2::A].into_iter()
    }
}

const LV2LINK: [(Kind2, Kind2); 5] = [
    (Kind2::U, Kind2::D),
    (Kind2::U, Kind2::A),
    (Kind2::D, Kind2::L),
    (Kind2::D, Kind2::R),
    (Kind2::R, Kind2::A),
];

fn lv2_build_pathes(from: Kind2, to: Kind2) -> Vec<Vec<Kind2>> {
    if from == to {
        return vec![vec![]];
    }
    let mut to_visit: Vec<Vec<Kind2>> = Vec::new();
    let mut pathes: Vec<Vec<Kind2>> = Vec::new();
    to_visit.push(vec![from]);
    while let Some(path) = to_visit.pop() {
        if path.last().unwrap() == &to {
            // path.remove(0);
            pathes.push(path);
            continue;
        }
        for (p, q) in LV2LINK.iter() {
            let r = if path.last().unwrap() == p && !path.contains(q) {
                q
            } else if path.last().unwrap() == q && !path.contains(p) {
                p
            } else {
                continue;
            };
            let mut path1 = path.clone();
            path1.push(*r);
            to_visit.push(path1);
        }
    }
    let len = pathes.iter().map(|l| l.len()).min().unwrap();
    pathes.retain(|l| l.len() == len);
    pathes
}

fn build_lv3_best_actions_to_push(
    lv3: Kind2,
    from: Kind2,
    to: Kind2,
) -> (Vec<Kind2>, Kind2, Kind2) {
    if from == to {
        return (vec![Kind2::A], Kind2::A, to);
    }
    let go = lv2_build_pathes(from, to);
    let (a, b) = lv2_path_to_lv2_actions(&go[0]);
    // dbg!(lv3, from, to, b);
    (a, lv3, to)
}

fn build_lv4_best_actions_to_push(from: Kind2, to: Kind2) -> (Vec<Kind2>, Kind2) {
    let mut go = lv2_build_pathes(from, to)[0].clone();
    go.push(Kind2::A);
    (go, to)
}

const LV1TOLV2: [((Kind1, Kind1), Kind2); 30] = [
    ((Kind1::K0, Kind1::K2), Kind2::U),
    ((Kind1::K0, Kind1::KA), Kind2::R),
    ((Kind1::K1, Kind1::K2), Kind2::R),
    ((Kind1::K1, Kind1::K4), Kind2::U),
    ((Kind1::K2, Kind1::K3), Kind2::R),
    ((Kind1::K2, Kind1::K5), Kind2::U),
    ((Kind1::K3, Kind1::K6), Kind2::U),
    ((Kind1::K3, Kind1::KA), Kind2::D),
    ((Kind1::K4, Kind1::K5), Kind2::R),
    ((Kind1::K4, Kind1::K7), Kind2::U),
    ((Kind1::K5, Kind1::K6), Kind2::R),
    ((Kind1::K5, Kind1::K8), Kind2::U),
    ((Kind1::K6, Kind1::K9), Kind2::U),
    ((Kind1::K7, Kind1::K8), Kind2::R),
    ((Kind1::K8, Kind1::K9), Kind2::R),
    ((Kind1::K2, Kind1::K0), Kind2::D),
    ((Kind1::KA, Kind1::K0), Kind2::L),
    ((Kind1::K2, Kind1::K1), Kind2::L),
    ((Kind1::K4, Kind1::K1), Kind2::D),
    ((Kind1::K3, Kind1::K2), Kind2::L),
    ((Kind1::K5, Kind1::K2), Kind2::D),
    ((Kind1::K6, Kind1::K3), Kind2::D),
    ((Kind1::KA, Kind1::K3), Kind2::D),
    ((Kind1::K5, Kind1::K4), Kind2::L),
    ((Kind1::K7, Kind1::K4), Kind2::D),
    ((Kind1::K6, Kind1::K5), Kind2::L),
    ((Kind1::K8, Kind1::K5), Kind2::D),
    ((Kind1::K9, Kind1::K6), Kind2::D),
    ((Kind1::K8, Kind1::K7), Kind2::L),
    ((Kind1::K9, Kind1::K8), Kind2::L),
];

fn lv1_path_to_lv2_actions(path: &[Kind1]) -> Vec<Kind2> {
    let mut ret = path
        .windows(2)
        .map(|v| {
            let p = v[0];
            let q = v[1];
            LV1TOLV2.iter().find(|(key, _)| key == &(p, q)).unwrap().1
        })
        .collect::<Vec<_>>();
    ret.push(Kind2::A);
    ret
}

const LV2TOLV2: [((Kind2, Kind2), Kind2); 10] = [
    ((Kind2::U, Kind2::D), Kind2::D),
    ((Kind2::U, Kind2::A), Kind2::R),
    ((Kind2::D, Kind2::L), Kind2::L),
    ((Kind2::D, Kind2::R), Kind2::R),
    ((Kind2::R, Kind2::A), Kind2::U),
    ((Kind2::D, Kind2::U), Kind2::U),
    ((Kind2::A, Kind2::U), Kind2::L),
    ((Kind2::L, Kind2::D), Kind2::R),
    ((Kind2::R, Kind2::D), Kind2::L),
    ((Kind2::A, Kind2::R), Kind2::D),
];

fn lv2_path_to_lv2_actions(path: &[Kind2]) -> (Vec<Kind2>, Kind2) {
    let mut p = vec![Kind2::A];
    p.append(&mut path.to_vec());
    let mut ret = path
        .windows(2)
        .map(|v| {
            let p = v[0];
            let q = v[1];
            LV2TOLV2.iter().find(|(key, _)| key == &(p, q)).unwrap().1
        })
        .collect::<Vec<_>>();
    let last = *ret.last().unwrap();
    ret.push(Kind2::A);
    (ret, last)
}

fn lv1_to_lv2_pathes(from: Kind1, to: Kind1) -> Vec<Vec<Kind2>> {
    lv1_build_pathes(from, to)
        .iter()
        .map(|path| {
            let mut path1 = vec![from];
            path1.append(&mut path.clone());
            let mut ret = path1
                .windows(2)
                .map(|pair| {
                    let p = pair[0];
                    let q = pair[1];
                    LV1TOLV2.iter().find(|(key, _)| key == &(p, q)).unwrap().1
                })
                .collect::<Vec<_>>();
            ret.push(Kind2::A);
            ret
        })
        .collect::<Vec<_>>()
}

#[derive(Clone, Debug, Default, Eq, PartialEq, Serialize)]
pub struct Puzzle {
    line: Vec<Vec<Kind1>>,
    level1path: HashMap<(Kind1, Kind1), Vec<Vec<Kind1>>>,
    lv1_to_lv2: HashMap<(Kind1, Kind1), Vec<Vec<Kind2>>>,
    level2path: HashMap<(Kind2, Kind2), Vec<Vec<Kind2>>>,
}

fn parse_kind1(s: &mut &str) -> PResult<Kind1> {
    one_of(&['0', '1', '2', '3', '4', '5', '6', '7', '8', '9', '0', 'A'])
        .map(|c| match c {
            '0' => Kind1::K0,
            '1' => Kind1::K1,
            '2' => Kind1::K2,
            '3' => Kind1::K3,
            '4' => Kind1::K4,
            '5' => Kind1::K5,
            '6' => Kind1::K6,
            '7' => Kind1::K7,
            '8' => Kind1::K8,
            '9' => Kind1::K9,
            'A' => Kind1::KA,
            _ => unreachable!(),
        })
        .parse_next(s)
}

fn parse_line(s: &mut &str) -> PResult<Vec<Kind1>> {
    repeat(1.., parse_kind1).parse_next(s)
}

fn parse(s: &mut &str) -> PResult<Vec<Vec<Kind1>>> {
    separated(1.., parse_line, newline).parse_next(s)
}

#[aoc(2024, 21)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, input: String) -> Result<String, ParseError> {
        self.line = parse(&mut input.as_str())?;
        Self::parsed()
    }
    fn end_of_data(&mut self) {
        // dbg!(&self.line);
        self.level2path = Kind2::iterator()
            .flat_map(|from| {
                Kind2::iterator()
                    .map(|to| ((from, to), lv2_build_pathes(from, to)))
                    .collect::<HashMap<(Kind2, Kind2), Vec<Vec<Kind2>>>>()
            })
            .collect::<HashMap<_, _>>();
        self.level1path = Kind1::iterator()
            .flat_map(|from| {
                Kind1::iterator()
                    .filter(|to| &from != to)
                    .map(|to| ((from, to), lv1_build_pathes(from, to)))
                    .collect::<HashMap<(Kind1, Kind1), Vec<Vec<Kind1>>>>()
            })
            .collect::<HashMap<_, _>>();
        // dbg!(lv1_build_pathes(Kind1::K5, Kind1::K3));
        // dbg!(lv1_to_lv2_pathes(Kind1::K5, Kind1::K3));
    }
    fn part1(&mut self) -> Self::Output1 {
        self.line
            .iter()
            .skip(3)
            .take(1)
            .map(|targets| {
                // これは数値パッドに打ち込みたいキーの並び
                let mut lv1_targets = vec![Kind1::KA];
                lv1_targets.append(&mut targets.clone());
                // dbg!(&lv1_targets);
                let a = lv1_targets
                    .windows(2)
                    .fold(
                        (0, Kind2::A, Kind2::A, Kind2::A),
                        |(len, lv4_pos, lv3_pos, lv2_pos), segment| {
                            lv1_build_pathes(segment[0], segment[1])
                                .iter()
                                .take(1)
                                .fold(
                                    (len, lv4_pos, lv3_pos, lv2_pos),
                                    |(len, lv4_pos, lv3_pos, lv2_pos), lv1_path| {
                                        // これはlv1で辿るキーの系列
                                        // println!("L1_path: {lv1_path:?}");
                                        let lv2_targets = lv1_path_to_lv2_actions(lv1_path);
                                        // これはlv2で押すべきキーの系列
                                        /* println!(
                                            "lv2_targets: {}, lv3:{}, lv2:{}",
                                            to_string(&lv2_targets),
                                            lv3_pos,
                                            lv2_pos,
                                        ); */
                                        // lv3に持ち上げ
                                        let lv3_targets = lv2_targets.iter().fold(
                                            (Vec::new(), lv4_pos, lv3_pos, lv2_pos),
                                            |(mut subs, lv4_pos, lv3_pos, lv2_pos), to| {
                                                let (mut t, lv3, lv2) =
                                                    build_lv3_best_actions_to_push(
                                                        lv3_pos, lv2_pos, *to,
                                                    );
                                                /* println!(
                                                    "lv2 segment: {}:{} => lv3_action: {} lv3:{}, lv2:{}",
                                                    lv2_pos,
                                                    to,
                                                    to_string(&t),
                                                    lv3,
                                                    lv2,
                                                ); */
                                                subs.append(&mut t);
                                                (subs, lv4_pos, lv3, lv2)
                                            },
                                        );
                                        // println!("lv3_targets: {}", to_string(&lv3_targets.0));

                                        let lv4_targets = lv3_targets.0.iter().fold(
                                            (Vec::new(), lv4_pos, lv3_targets.1, lv3_targets.2),
                                            |(mut subs, lv4_pos, lv3_pos, lv2_pos), to| {
                                                let (mut t, lv4, lv3) =
                                                    build_lv3_best_actions_to_push(
                                                        lv4_pos, lv3_pos, *to,
                                                    );
                                                /* println!(
                                                    "lv3 segment: {}:{} => lv4_action: {} lv4:{}, lv3:{}",
                                                    lv3_pos,
                                                    to,
                                                    to_string(&t),
                                                    lv4,
                                                    lv3,
                                                ); */
                                                subs.append(&mut t);
                                                (subs, lv4, lv3, lv2_pos)
                                            },
                                        );
                                        // println!("lv4_targets: {}", to_string(&lv4_targets.0));
                                        (
                                            len + lv4_targets.0.len(),
                                            lv4_targets.1,
                                            lv4_targets.2,
                                            lv4_targets.3,
                                        )
                                    },
                                )
                        },
                    )
                    .0;
                let b = targets
                    .iter()
                    .filter(|k| **k != Kind1::KA)
                    .fold(0, |acc, k| acc * 10 + (*k as usize));
                dbg!(a) * dbg!(b)
            })
            .map(|n| dbg!(n))
            .sum::<usize>()
    }
    fn part2(&mut self) -> Self::Output2 {
        2
    }
}
