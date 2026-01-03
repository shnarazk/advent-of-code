//! <https://adventofcode.com/2025/day/10>
#![allow(dead_code)]
#![allow(unused_imports)]
// #![allow(unused_variables)]
use {
    crate::{
        framework::{AdventOfCode, ParseError, aoc},
        math::{gcd, lcm},
    },
    rayon::prelude::*,
    rustc_data_structures::fx::{FxHashMap, FxHasher},
    std::{
        cmp::{Ordering, Reverse},
        collections::{BinaryHeap, HashMap, HashSet},
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

#[aoc(2025, 10)]
impl AdventOfCode for Puzzle {
    fn prepare(&mut self, mut input: &str) -> Result<(), ParseError> {
        self.line = parser::parse(&mut input)?;
        self.line.iter().take(10).for_each(|(_, buttons, goal)| {
            let ws = buttons.iter().map(|l| l.len()).collect::<Vec<_>>();
            let total = goal.iter().sum::<usize>();
            let g = ws.iter().skip(1).fold(ws[0], |acc, n| gcd(acc, *n));
            dbg!(g, total);
        });
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
            .par_iter()
            .take(10)
            .map(|(_, buttons, goal)| {
                let num_buttons = buttons.len();
                let mut sorted_buttons = buttons.clone();
                sorted_buttons.sort_unstable_by_key(|l| l.len());
                sorted_buttons.reverse();
                let mut to_visit: BinaryHeap<Reverse<State>> = BinaryHeap::new();
                to_visit.push(Reverse(State {
                    remain: goal.iter().sum::<usize>(),
                    counts: vec![0; num_buttons],
                }));
                while let Some(Reverse(state)) = to_visit.pop() {
                    for (_, _button) in state.counts.iter().enumerate() {
                        let mut s = state.clone();
                        // for bi in button.iter() {
                        //     s[*bi] += 1;
                        //     if s[*bi] > goal[*bi] {
                        //         continue 'next_button;
                        //     }
                        // }
                        if s.counts == *goal {
                            return dbg!(0);
                        }
                        // for n in next.iter() {
                        //     if (0..size).all(|i| s1[i] <= n[i]) {
                        //         continue 'next_button;
                        //     }
                        // }
                        if to_visit.iter().find(|Reverse(r)| *r == s).is_none() {
                            to_visit.push(Reverse(s));
                        }
                    }
                }
                unreachable!()
            })
            .sum::<usize>()
    }
}

fn traverse(
    buttons: &[Vec<usize>],
    goal: &Vec<usize>,
    counts: Vec<Option<usize>>,
    levels: &Vec<usize>,
    memo: &mut HashSet<Vec<usize>>,
) -> Option<usize> {
    if *levels == *goal {
        return Some(counts.iter().flatten().sum::<usize>());
    } else if let Some(cursor) = counts.iter().position(|n| n.is_none()) {
        let mut max_assign = buttons[cursor]
            .iter()
            .map(|li| goal[*li] - levels[*li])
            .min();
        // let tmp = max_assign;
        while let Some(count) = max_assign {
            let mut new_counts = counts.clone();
            new_counts[cursor] = max_assign;
            let mut new_levels = levels.clone();
            for li in buttons[cursor].iter() {
                new_levels[*li] += count;
            }
            // if memo.contains(&new_levels) {
            //     return None;
            // }
            if let Some(ans) = traverse(buttons, goal, new_counts, &new_levels, memo) {
                return Some(ans);
            }
            max_assign = count.checked_sub(1);
        }
        // if let Some(n) = tmp {
        //     let mut l = levels.clone();
        //     for li in buttons[cursor].iter() {
        //         l[*li] += n;
        //     }
        //     memo.insert(l);
        // }
    }
    None
}

fn f(v: &[usize], count: Vec<usize>, n: usize) -> Option<Vec<usize>> {
    if n == 0 {
        println!("{count:?}");
        return None;
    }
    if v.is_empty() {
        return None;
    }
    for i in (0..=n / v[0]).rev() {
        let mut c = count.clone();
        c.push(i);
        if let Some(mut a) = f(&v[1..], c, n - v[0] * i) {
            a.push(i);
            return Some(a);
        }
    }
    None
}
