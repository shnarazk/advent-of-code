//! <https://adventofcode.com/2025/day/10>
use {
    crate::framework::{AdventOfCode, ParseError, aoc},
    microlp::{ComparisonOp, OptimizationDirection, Problem, Variable},
    rayon::prelude::*,
    std::{
        cmp::Ordering,
        collections::{HashMap, HashSet},
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
            .iter()
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
    order_to_index
        .into_iter()
        .map(|(_, n)| n)
        .collect::<Vec<_>>()
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

/*
goal: [209, 264, 67, 234, 249, 232, 234, 233, 59, 84]
buttons: [[1, 2, 5, 6, 7, 8, 9], [2, 4, 9], [3, 4, 6, 7, 8, 9], [0, 5], [0, 1, 2, 7, 9], [0, 1, 4, 5, 7, 9], [1, 3, 8], [1, 2, 3, 4, 5, 6, 8, 9], [1, 2, 3, 4, 6, 8, 9], [0, 1, 2, 3, 4, 5, 7, 8, 9], [0, 1, 3, 4, 5, 6, 7], [1, 2, 4, 5, 6, 7, 9], [0, 1, 2, 3, 4, 5, 8, 9]]
order_to_index: [9, 12, 7, 11, 10, 8, 0, 5, 2, 4, 6, 1, 3]
final_affector: [[], [2, 4, 9], [6], [0, 5], [7], [], [1, 3, 8], [], [], [], [], [], []]
available_bands: [(0, 60), (0, 68), (0, 60), (0, 210), (0, 68), (0, 85), (0, 60), (0, 60), (0, 60), (0, 60), (0, 210), (0, 68), (0, 60)]
*/
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
    let mut resolved_lights: HashSet<usize> = HashSet::new();
    let mut checkpoint: usize = usize::MAX;
    {
        let mut possibility: usize = 1;
        'next: for (order, button_id) in order_to_index.iter().enumerate() {
            for light_id in final_affector[*button_id].iter() {
                resolved_lights.insert(*light_id);
            }
            possibility = 1;
            for (light_id, band) in available_bands.iter().enumerate() {
                if !resolved_lights.contains(&light_id) {
                    possibility *= band.1 - band.0;
                    if possibility > 400_000_000 {
                        continue 'next;
                    }
                }
            }
            checkpoint = order;
            break;
        }
        println!(
            "check at {} for {} possibilities: {:?}",
            checkpoint,
            possibility,
            &order_to_index[0..checkpoint]
        );
    }
    let mut checked_patterns: HashMap<Vec<usize>, Option<usize>> = HashMap::new();
    let mut limits = available_bands.clone();
    let mut button_toggles = vec![0; num_buttons];
    let mut light_flips = vec![0; num_lights];
    let mut key: Vec<usize> = Vec::new();
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
        // Now we have a cache at a specific order (= checkpoint), check it.
        if target_order == checkpoint {
            key = light_flips
                .iter()
                .enumerate()
                .filter(|(i, _)| !resolved_lights.contains(i))
                .map(|(_, n)| *n)
                .collect();
            if let Some(checked) = checked_patterns.get(&key) {
                if let Some(n) = checked {
                    return *n;
                } else {
                    target_order -= 1;
                    limits[index] = available_bands[index];
                    button_toggles[index] = 0;
                    continue 'shift_target;
                }
            }
        }
        'next_value: for num_toggles in (limits[index].0..limits[index].1).rev() {
            button_toggles[index] = num_toggles;
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
                    let ans = button_toggles.iter().sum::<usize>();
                    println!("found: {:?} => {}", &button_toggles, ans);
                    // TODO: maybe we need to keep to traverse after updating the best record
                    if let Some(n) = checked_patterns.get(&key.clone()) {
                        if let Some(a) = n {
                            if ans < *a {
                                checked_patterns.insert(key.clone(), Some(ans));
                            }
                        } else {
                            unreachable!();
                        }
                    } else {
                        checked_patterns.insert(key.clone(), Some(ans));
                    }
                    continue;
                    // return dbg!(button_toggles.into_iter().sum::<usize>());
                }
                Ordering::Greater => {
                    continue;
                }
                Ordering::Less => {
                    if target_order + 1 == num_buttons {
                        break;
                    }
                    target_order += 1;
                    // println!("shift to next");
                    limits[index].1 = num_toggles;
                    continue 'shift_target;
                }
            }
        }
        // debug_assert!(target_order > 0);
        if target_order == 0 {
            break;
        }
        target_order -= 1;
        limits[index] = available_bands[index];
        button_toggles[index] = 0;
        if target_order == checkpoint {
            // TODO: at one of final affectors, we can remember the combination of fixed light flips not
            // to search the subspace again!
            if !checked_patterns.contains_key(&key) {
                checked_patterns.insert(key.clone(), None);
            }
        }
        // println!("shift back to {}", target_order);
    }
    checked_patterns
        .into_values()
        .filter_map(|v| v)
        .min()
        .unwrap_or(0)
}
