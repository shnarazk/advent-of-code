//! <https://adventofcode.com/2025/day/10>
#![allow(dead_code)]
// #![allow(unused_imports)]
// #![allow(unused_variables)]
use {
    crate::{
        framework::{AdventOfCode, ParseError, aoc},
        // math::{gcd, lcm},
    },
    // rayon::prelude::*,
    rustc_data_structures::fx::{FxHashSet, FxHasher},
    std::{
        cmp::{Ordering, Reverse},
        collections::{BinaryHeap, HashSet},
        hash::BuildHasherDefault,
    },
};

type Spec = (Vec<bool>, Vec<Vec<usize>>, Vec<usize>);

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Spec>,
}

mod parser {
    use {
        super::Spec,
        crate::parser::parse_usize,
        winnow::{
            ModalResult, Parser,
            ascii::newline,
            combinator::{repeat, separated, seq},
            token::one_of,
        },
    };

    fn parse_indicator(s: &mut &str) -> ModalResult<Vec<bool>> {
        seq!(_: "[", repeat(1.., one_of(['#', '.']).map(|s: char| s == '#')), _: "]")
            .map(|(v,)| v)
            .parse_next(s)
    }
    fn parse_nums(s: &mut &str) -> ModalResult<Vec<usize>> {
        separated(1.., parse_usize, ",").parse_next(s)
    }
    fn parse_buttons(s: &mut &str) -> ModalResult<Vec<Vec<usize>>> {
        separated(1.., seq!(_: "(", parse_nums, _:")").map(|(v,)| v), " ").parse_next(s)
    }
    fn parse_requirement(s: &mut &str) -> ModalResult<Vec<usize>> {
        seq!(_: "{", parse_nums, _:"}").map(|(v,)| v).parse_next(s)
    }
    fn parse_line(s: &mut &str) -> ModalResult<Spec> {
        seq!(
            parse_indicator, _: " ",
            parse_buttons, _: " ",
            parse_requirement,
        )
        .parse_next(s)
    }
    pub fn parse(s: &mut &str) -> ModalResult<Vec<Spec>> {
        separated(1.., parse_line, newline).parse_next(s)
    }
}

#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
struct State {
    remain: usize,
    counts: Vec<usize>,
}

impl PartialOrd for State {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.remain.partial_cmp(&other.remain)
    }
}

impl Ord for State {
    fn cmp(&self, other: &Self) -> Ordering {
        self.remain.cmp(&other.remain)
    }
}

impl State {
    fn sum(&self, buttons: &[Vec<usize>], n: usize) -> Vec<usize> {
        let mut result = vec![0; n];
        for (bi, n) in self.counts.iter().enumerate() {
            for i in buttons[bi].iter() {
                result[*i] += *n as usize;
            }
        }
        result
    }
}

fn exceeds(values: &[usize], dist: &[usize], goal: &[usize]) -> bool {
    assert_eq!(values.len(), goal.len());
    values
        .iter()
        .enumerate()
        .any(|(i, n)| dist.contains(&(i as usize)) as usize + n > goal[i])
}

#[aoc(2025, 10)]
impl AdventOfCode for Puzzle {
    fn prepare(&mut self, mut input: &str) -> Result<(), ParseError> {
        self.line = parser::parse(&mut input)?;
        dbg!(self.line.iter().map(|s| s.2.len()).max());
        dbg!(
            self.line
                .iter()
                .map(|s| {
                    let mut p = s.2.clone();
                    p.sort();
                    p.reverse();
                    [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]
                        .iter()
                        .zip(p.iter())
                        .map(|(_a, b)| b * 1)
                        // .product::<usize>()
                        .max()
                })
                .max()
        );
        // self.line.iter().take(10).for_each(|(_, buttons, goal)| {
        //     let ws = buttons.iter().map(|l| l.len()).collect::<Vec<_>>();
        //     let total = goal.iter().sum::<usize>();
        //     let g = ws.iter().skip(1).fold(ws[0], |acc, n| gcd(acc, *n));
        //     dbg!(g, total);
        // });
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        self.line
            .iter()
            .map(|(goal, buttons, _)| {
                let mut checked: HashSet<Vec<bool>> = HashSet::new();
                let mut to_visit: HashSet<Vec<bool>> = HashSet::new();
                let mut next: HashSet<Vec<bool>> = HashSet::new();
                to_visit.insert(vec![false; goal.len()]);
                for i in 1_usize.. {
                    next.clear();
                    for s in to_visit.iter() {
                        if checked.contains(s) {
                            continue;
                        }
                        checked.insert(s.clone());
                        for button in buttons.iter() {
                            let mut s1 = s.clone();
                            for bi in button.iter() {
                                s1[*bi] = !s1[*bi];
                            }
                            if s1 == *goal {
                                return i;
                            }
                            if !checked.contains(&s1) {
                                next.insert(s1);
                            }
                        }
                    }
                    std::mem::swap(&mut next, &mut to_visit);
                }
                unreachable!()
            })
            .sum::<usize>()
    }
    fn part2(&mut self) -> Self::Output2 {
        self.line
            .iter()
            .take(10)
            .map(|(_, buttons, goal)| {
                let goal = goal.iter().map(|n| *n as usize).collect::<Vec<_>>();
                // let scale: usize = 10000;
                let mut counter = 0;
                let num_buttons = buttons.len();
                let goal_len = goal.len();
                // let button_weight: Vec<usize> =
                //     buttons.iter().map(|l| l.len()).collect::<Vec<usize>>();
                // let mut distribution = buttons.clone();
                // distribution.sort_unstable_by_key(|l| l.len());
                // distribution.reverse();
                let mut visited: FxHashSet<Vec<usize>> =
                    HashSet::<_, BuildHasherDefault<FxHasher>>::default();
                let mut to_visit: BinaryHeap<Reverse<State>> = BinaryHeap::new();
                to_visit.push(Reverse(State {
                    remain: goal.iter().map(|d| *d).sum::<usize>(),
                    counts: vec![0; num_buttons],
                }));
                while let Some(Reverse(state)) = to_visit.pop() {
                    let values = state.sum(buttons, goal_len);
                    if values == *goal {
                        return dbg!(state.counts.into_iter().sum::<usize>());
                    }
                    if state.remain == 0 || visited.contains(&values) {
                        continue;
                    }
                    let sum = state.counts.iter().sum::<usize>();
                    if counter < sum {
                        counter = sum;
                        dbg!(&state);
                    }
                    // assert_eq!(values.len(), goal.len());
                    for (bi, distribution) in buttons.iter().enumerate() {
                        if exceeds(&values, &distribution, &goal) {
                            continue;
                        }
                        let mut s = state.clone();
                        s.counts[bi] += 1;
                        // if s.remain < distribution.len() {
                        //     panic!(
                        //         "{:?} < {:?} :: {:?}, {}: {:?}",
                        //         s, goal, buttons, bi, distribution
                        //     );
                        // }
                        let v = s.sum(buttons, goal_len);
                        s.remain = goal
                            .iter()
                            .zip(v.iter())
                            .map(|(a, b)| (*a - *b).pow(1) + 1)
                            .product::<usize>()
                        // * goal
                        //     .iter()
                        //     .zip(v.iter())
                        //     .filter(|(a, b)| *a != *b)
                        //     .count()
                            // / s.counts
                            //     .iter()
                            //     .enumerate()
                            //     .map(|(i, c)| *c * button_weight[i])
                            //     .sum::<usize>();
                            // * s.counts
                            //     .iter()
                            //     .sum::<usize>().isqrt();
                            ;
                        if !visited.contains(&v) {
                            to_visit.push(Reverse(s));
                        }
                    }
                    visited.insert(values);
                }
                unreachable!()
            })
            .sum::<usize>()
    }
}
