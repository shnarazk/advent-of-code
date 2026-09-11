//! <https://adventofcode.com/2025/day/10>
use {
    crate::{
        framework::{AdventOfCode, ParseError, aoc},
        math::permutations,
    },
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
            .iter()
            .enumerate()
            .map(|(i, (_, buttons, goal))| {
                dbg!(i);
                let new = solve2(buttons, goal);
                assert_eq!(solve(buttons, goal), new);
                new
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

fn _weight_order(buttons: &[Vec<usize>]) -> Vec<usize> {
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

fn compare(flips: &[u16], goal: &[u16]) -> Ordering {
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

/// level-1まで確定した部分解に対して one step展開する。
fn memoized_solve2(
    level: usize,
    best: &mut usize,
    checked_patterns: &mut HashSet<(u8, usize, Vec<u16>)>,
    // 先に使ったボタンはもう使えない閾値となるレベルを集めたもの
    basin: &[usize],
    button_toggles_pre: &[usize],
    order_to_index: &[usize],
    final_affector: &[Vec<usize>],
    available_bands: &[(usize, usize)],
    buttons: &[Vec<usize>],
    goal: &[u16],
) {
    if level == buttons.len() {
        return;
    }
    let index = order_to_index[level];
    let mut button_toggles = button_toggles_pre.to_vec();
    let mut light_flips: Vec<u16> = vec![0; goal.len()];
    for i in order_to_index.iter().take(level) {
        for light_id in buttons[*i].iter() {
            assert!(light_flips[*light_id] as usize + button_toggles[*i] < 1024);
            light_flips[*light_id] += button_toggles[*i] as u16;
        }
    }
    let to_memoize = level + 1 < buttons.len() && basin.contains(&level);
    for light_id in buttons[index].iter() {
        assert!(light_flips[*light_id] as usize + available_bands[index].1 < 1024);
        light_flips[*light_id] += available_bands[index].1 as u16;
    }
    'next_value: for num_toggles in (available_bands[index].0..available_bands[index].1).rev() {
        button_toggles[index] = num_toggles;
        for light_id in buttons[index].iter() {
            assert!(light_flips[*light_id] > 0);
            light_flips[*light_id] -= 1;
        }
        for light_id in final_affector[index].iter() {
            match light_flips[*light_id].cmp(&goal[*light_id]) {
                Ordering::Less => break 'next_value,
                Ordering::Equal => (),
                Ordering::Greater => continue 'next_value,
            }
        }
        let ans = button_toggles.iter().sum::<usize>();
        if ans > *best {
            continue;
        }
        if to_memoize && checked_patterns.contains(&(level as u8, ans, light_flips.clone())) {
            continue;
        }
        match compare(&light_flips, goal) {
            Ordering::Equal => {
                if ans < *best {
                    *best = ans;
                    println!(
                        "- {best:>5}/ {:>7}| toggles: {button_toggles:?}",
                        checked_patterns.len()
                    );
                }
            }
            Ordering::Greater => {}
            Ordering::Less => {
                memoized_solve2(
                    level + 1,
                    best,
                    checked_patterns,
                    basin,
                    &button_toggles,
                    order_to_index,
                    final_affector,
                    available_bands,
                    buttons,
                    goal,
                );
            }
        }
        if to_memoize {
            checked_patterns.insert((level as u8, ans, light_flips.clone()));
        }
    }
}

fn best_button_order(buttons: &[Vec<usize>], affectors: &[Vec<usize>], goal: &[u16]) -> Vec<usize> {
    let num_buttons: usize = buttons.len();
    let num_lights: usize = goal.len();
    let perms = permutations(0, num_buttons - 1);
    let mut best_order: Vec<usize> = perms[0].clone();
    let mut best_value: f64 = f64::MAX;
    'next_cand: for order in perms.into_iter() {
        // evaluate `order`
        let mut e: f64 = 0.0;
        let mut used_button = vec![false; num_buttons];
        let mut nomore_affector = vec![false; num_lights];
        for (i, b_id) in order.iter().enumerate() {
            used_button[*b_id] = true;
            for l_id in 0..num_lights {
                if !nomore_affector[l_id] && affectors[l_id].iter().all(|b| used_button[*b]) {
                    nomore_affector[l_id] = true;
                    let point = i as f64 / goal[l_id] as f64;
                    e += point;
                    if best_value < e {
                        continue 'next_cand;
                    }
                }
            }
        }
        if e < best_value {
            best_value = e;
            best_order = order;
            println!("{best_order:?} ({best_value:>5.5})");
        }
    }
    return best_order;
}

fn solve2(buttons: &[Vec<usize>], goal: &[usize]) -> usize {
    let num_buttons: usize = buttons.len();
    let num_lights: usize = goal.len();
    assert!(goal.iter().all(|n| *n <= 1024));
    let goal_u16 = goal.iter().map(|n| *n as u16).collect::<Vec<u16>>();
    let affectors: Vec<Vec<usize>> = {
        let mut tmp: Vec<Vec<usize>> = vec![Vec::new(); num_lights];
        for (b_id, lights) in buttons.iter().enumerate() {
            for l_id in lights.iter() {
                tmp[*l_id].push(b_id);
            }
        }
        tmp
    };
    let available_bands: Vec<(usize, usize)> = lower_limits(buttons, goal)
        .iter()
        .zip(upper_limits(buttons, goal).iter())
        .map(|(l, u)| (*l, *u))
        .collect::<Vec<_>>();
    let order_to_index = best_button_order(&buttons, &affectors, &goal_u16);
    // let order_to_index = weight_order(buttons);
    let final_affector = final_affectors(buttons, &order_to_index, num_lights);
    let mut basin: Vec<usize> = Vec::new();
    {
        let btns = order_to_index
            .iter()
            .map(|i| buttons[*i].clone())
            .collect::<Vec<_>>();
        let bands = order_to_index
            .iter()
            .map(|i| available_bands[*i].clone())
            .collect::<Vec<_>>();
        for level in 0..num_buttons {
            let mut fixed = Vec::new();
            for b_id in order_to_index.iter().take(level + 1) {
                for l_id in final_affector[*b_id].iter() {
                    fixed.push(*l_id);
                }
            }
            if order_to_index
                .iter()
                .take(level + 1)
                .all(|b_id| buttons[*b_id].iter().any(|l_id| fixed.contains(l_id)))
            {
                basin.push(level);
            }
        }
        println!(
            "\
        - goal           : {goal:?}\n\
        - affectors      : {affectors:?}\n\
        - order_to_index : {order_to_index:?}\n\
        - buttons        (ordered): {btns:?}\n\
        - final_affector (ordered): {final_affector:?}\n\
        - available_bands(ordered): {bands:?}\n\
        - basin          (ordered): {basin:?}"
        );
    }
    let mut checked_patterns: HashSet<(u8, usize, Vec<u16>)> = HashSet::new();
    let button_toggles = vec![0; num_buttons];
    let mut best = usize::MAX;
    memoized_solve2(
        0,
        &mut best,
        &mut checked_patterns,
        &basin,
        &button_toggles,
        &order_to_index,
        &final_affector,
        &available_bands,
        &buttons,
        &goal_u16,
    );
    best
}
