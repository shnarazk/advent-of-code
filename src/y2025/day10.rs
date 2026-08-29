//! <https://adventofcode.com/2025/day/10>
use {
    crate::framework::{AdventOfCode, ParseError, aoc},
    microlp::{ComparisonOp, OptimizationDirection, Problem, Variable},
    rayon::prelude::*,
    std::{cmp::Ordering, collections::HashSet},
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
            // .take(2)
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

fn weight_order(buttons: &[Vec<usize>]) -> Vec<usize> {
    let num_buttons: usize = buttons.len();
    let mut order_to_index = vec![(0, 0); num_buttons];
    for (i, button) in buttons.iter().enumerate() {
        order_to_index[i] = (button.len(), i);
    }
    order_to_index.sort();
    order_to_index.reverse();
    order_to_index.iter().map(|(_, n)| *n).collect::<Vec<_>>()
}

fn upper_limits(buttons: &[Vec<usize>], goal: &[usize]) -> Vec<usize> {
    buttons
        .iter()
        .map(|targets| targets.iter().map(|i| goal[*i]).min().unwrap_or_default() + 1)
        .collect::<Vec<usize>>()
}

fn lower_limits(buttons: &[Vec<usize>], goal: &[usize]) -> Vec<usize> {
    let mut affectors = vec![Vec::new(); goal.len()];
    for (button_id, targets) in buttons.iter().enumerate() {
        for light_id in targets {
            affectors[*light_id].push(button_id);
        }
    }
    let mut result = vec![0; buttons.len()];
    for (light_id, bs) in affectors.iter().enumerate() {
        if bs.len() == 1 {
            result[bs[0]] = goal[light_id];
        }
    }
    result
}

fn final_affectors(buttons: &[Vec<usize>], order: &[usize], num_lights: usize) -> Vec<Vec<usize>> {
    let mut last_affector: Vec<usize> = vec![0; num_lights];
    for button_id in order.iter() {
        for light_id in buttons[*button_id].iter() {
            last_affector[*light_id] = *button_id;
        }
    }
    // println!("last_affector: {:?}", &last_affector);
    (0..buttons.len())
        .map(|button_id| {
            last_affector
                .iter()
                .enumerate()
                .filter(|(_, b)| **b == button_id)
                .map(|(i, _)| i)
                .collect::<Vec<usize>>()
        })
        .collect::<Vec<Vec<usize>>>()
}

fn compare(flips: &[usize], goal: &[usize]) -> Ordering {
    let mut ord = Ordering::Equal;
    for (f, g) in flips.iter().zip(goal.iter()) {
        match f.cmp(g) {
            Ordering::Greater => return Ordering::Greater,
            o => {
                ord = ord.min(o);
            }
        }
    }
    ord
}

fn solve2(buttons: &[Vec<usize>], goal: &[usize]) -> usize {
    println!("goal: {:?}", &goal);
    println!("buttons: {:?}", &buttons);
    let num_buttons: usize = buttons.len();
    let num_lights: usize = goal.len();
    let mut target_order: usize = 0;
    let order_to_index = weight_order(buttons);
    println!("order_to_index: {:?}", &order_to_index);
    let final_affector = final_affectors(buttons, &order_to_index, num_lights);
    println!("final_affector: {:?}", &final_affector);
    let available_bands: Vec<(usize, usize)> = lower_limits(buttons, goal)
        .iter()
        .zip(upper_limits(buttons, goal).iter())
        .map(|(l, u)| (*l, *u))
        .collect::<Vec<_>>();
    println!("available_bands: {:?}", &available_bands);
    let mut limits = available_bands.clone();
    let mut button_toggles = vec![0; num_buttons];
    // let mut best = usize::MAX;
    let mut light_flips = vec![0; num_lights];
    'shift_target: loop {
        let index = order_to_index[target_order];
        debug_assert_eq!(light_flips[index], 0);
        light_flips.fill(0);
        button_toggles[index] = limits[index].1;
        for (button_id, n) in button_toggles.iter().enumerate() {
            for light_id in buttons[button_id].iter() {
                light_flips[*light_id] += n;
            }
        }
        'next_value: for lim in (limits[index].0..limits[index].1).rev() {
            button_toggles[index] = lim;
            for light_id in buttons[index].iter() {
                light_flips[*light_id] -= 1;
            }
            for light_id in final_affector[index].iter() {
                match light_flips[*light_id].cmp(&goal[*light_id]) {
                    Ordering::Less => break 'next_value,
                    Ordering::Equal => (),
                    Ordering::Greater => continue 'next_value,
                }
            }
            // println!("{:?} => {:?}", &toggles, &flips);
            match compare(&light_flips, goal) {
                Ordering::Equal => {
                    println!("{:?}", &button_toggles);
                    return dbg!(button_toggles.iter().copied().sum::<usize>());
                }
                Ordering::Greater => {
                    continue;
                }
                Ordering::Less => {
                    // let dist = flips
                    //     .iter()
                    //     .zip(goal.iter())
                    //     .map(|(a, b)| *b - *a)
                    //     .sum::<usize>();
                    // if dist < best {
                    //     best = dbg!(dist);
                    // }
                    if target_order + 1 == num_buttons {
                        break;
                    }
                    target_order += 1;
                    // println!("shift to next");
                    limits[index].1 = lim;
                    continue 'shift_target;
                }
            }
        }
        if target_order == 0 {
            return 0;
        }
        target_order -= 1;
        limits[index] = available_bands[index];
        button_toggles[index] = 0;
        // println!("shift back to {}", target_order);
    }
}
