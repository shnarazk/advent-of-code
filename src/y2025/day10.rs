//! <https://adventofcode.com/2025/day/10>
use {
    crate::framework::{AdventOfCode, ParseError, aoc},
    microlp::{ComparisonOp, OptimizationDirection, Problem, Variable},
    rayon::prelude::*,
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

#[aoc(2025, 10)]
impl AdventOfCode for Puzzle {
    fn prepare(&mut self, mut input: &str) -> Result<(), ParseError> {
        self.line = parser::parse(&mut input)?;
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        self.line
            .par_iter()
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
            .map(|(_, buttons, goal)| {
                if true {
                    solve2(buttons, goal)
                } else {
                    solve(buttons, goal)
                }
            })
            .sum::<usize>()
    }
}

fn solve(buttons: &[Vec<usize>], goals: &[usize]) -> usize {
    let mut problem = Problem::new(OptimizationDirection::Minimize);
    let mut variables: Vec<Variable> = Vec::new();
    for _ in 0..buttons.len() {
        let b = problem.add_integer_var(1.0, (0, i32::MAX));
        variables.push(b);
    }
    for (gi, g) in goals.iter().enumerate() {
        let mut group: Vec<(Variable, f64)> = Vec::new();
        for (bi, b) in buttons.iter().enumerate() {
            if b.contains(&gi) {
                group.push((variables[bi], 1.0));
            }
        }
        problem.add_constraint(&group, ComparisonOp::Eq, *g as f64);
    }

    let Ok(solution) = problem.solve().unwrap().into_solution() else {
        panic!();
    };
    variables
        .iter()
        .map(|b| solution[*b])
        .map(|f| f.round() as usize)
        .sum::<usize>()
}

#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
struct State {
    /// distance to goal. smaller is better.
    remain: usize,
    /// the number of times each button is pressed.
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
    /// - `buttons` is a mapping from `id` to `[affecting_light_id]`
    /// - `n` is the number of lights
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

/// returns `true` if `values + dist` exceeds `goal` by any amount
fn exceeds(values: &[usize], dist: &[usize], goal: &[usize]) -> bool {
    debug_assert_eq!(values.len(), goal.len());
    values
        .iter()
        .enumerate()
        .any(|(i, n)| dist.contains(&(i as usize)) as usize + n > goal[i])
}

fn solve2(buttons: &[Vec<usize>], goal: &[usize]) -> usize {
    // let scale: usize = 10000;
    let mut counter = 0;
    let num_buttons = buttons.len();
    let goal_len = goal.len();
    // let button_weight: Vec<usize> =
    //     buttons.iter().map(|l| l.len()).collect::<Vec<usize>>();
    // let mut distribution = buttons.clone();
    // distribution.sort_unstable_by_key(|l| l.len());
    // distribution.reverse();
    let mut visited: FxHashSet<Vec<usize>> = HashSet::<_, BuildHasherDefault<FxHasher>>::default();
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
}
