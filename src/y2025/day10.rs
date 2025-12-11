//! <https://adventofcode.com/2025/day/10>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{self, AdventOfCode, ParseError, aoc},
        math::{gcd, lcm},
    },
    microlp::{ComparisonOp, OptimizationDirection, Problem, Variable},
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
            ascii::{alpha1, newline, space1},
            combinator::{alt, repeat, separated, seq},
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
        demo();
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
                let mut sorted = buttons.clone();
                sorted.sort_unstable_by_key(|l| l.len());
                sorted.reverse();

                let b = sorted[0].len();
                let s = sorted[sorted.len() - 1].len();
                let memo: HashSet<Vec<usize>> = HashSet::new();
                // let range = dbg!(b - s);

                let counts: Vec<Option<usize>> = vec![None; buttons.len()];
                let levels = vec![0_usize; goal.len()];

                // dbg!(traverse(&sorted, goal, counts, &levels, &mut memo).expect(""))
                0
                /*
                let size = goal.len();
                let mut to_visit: HashSet<Vec<usize>> = HashSet::new();
                let mut next: HashSet<Vec<usize>> = HashSet::new();
                to_visit.insert(vec![0; goal.len()]);
                for i in 1_usize.. {
                    if i % 10 == 0 {
                        dbg!(to_visit.len());
                    }
                    next.clear();
                    for s in to_visit.iter() {
                        'next_button: for button in buttons.iter() {
                            let mut s1 = s.clone();
                            for bi in button.iter() {
                                s1[*bi] += 1;
                                if s1[*bi] > goal[*bi] {
                                    continue 'next_button;
                                }
                            }
                            if s1 == *goal {
                                return dbg!(i);
                            }
                            // for n in next.iter() {
                            //     if (0..size).all(|i| s1[i] <= n[i]) {
                            //         continue 'next_button;
                            //     }
                            // }
                            if to_visit.contains(&s1) {
                                dbg!();
                            }
                            next.insert(s1);
                        }
                    }
                    std::mem::swap(&mut next, &mut to_visit);
                    assert!(!to_visit.is_empty());
                }
                unreachable!()
                */
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
        let tmp = max_assign;
        while let Some(count) = max_assign {
            // if cursor == 0 {
            //     dbg!(count, memo.len());
            // }
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

// (3,4,5,7) (2,4,5,6,7) (1,4,7) (1,3,4,7) (1,2,3,4,5,7) (7) (1,2,3,6) (0,1,3,6,7)
// {4,59,39,250,242,220,26,250}
fn demo() {
    let mut problem = Problem::new(OptimizationDirection::Minimize);
    let mut buttons: Vec<Variable> = Vec::new();
    for i in 0..8 {
        let b = problem.add_integer_var(1.0, (0, i32::MAX));
        buttons.push(b);
    }
    // (3,4,5,7) (2,4,5,6,7) (1,4,7) (1,3,4,7) (1,2,3,4,5,7) (7) (1,2,3,6) (0,1,3,6,7)
    let config: Vec<Vec<usize>> = vec![
        vec![3, 4, 5, 7],
        vec![2, 4, 5, 6, 7],
        vec![1, 4, 7],
        vec![1, 3, 4, 7],
        vec![1, 2, 3, 4, 5, 7],
        vec![7],
        vec![1, 2, 3, 6],
        vec![0, 1, 3, 6, 7],
    ];
    let goals: Vec<usize> = vec![4, 59, 39, 250, 242, 220, 26, 250];
    for (gi, g) in goals.iter().enumerate() {
        let mut group: Vec<(Variable, f64)> = Vec::new();
        for (bi, b) in config.iter().enumerate() {
            if b.contains(&gi) {
                group.push((buttons[bi], 1.0));
            }
        }
        problem.add_constraint(&group, ComparisonOp::Eq, *g as f64);
    }

    let solution = problem.solve().unwrap();
    for (vi, v) in buttons.iter().enumerate() {
        println!("b{vi} = {:?}", solution[*v]);
    }
    println!("done");
}
