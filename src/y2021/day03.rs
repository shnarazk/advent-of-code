//! <https://adventofcode.com/2021/day/3>
use crate::{
    framework::{AdventOfCode, ParseError, aoc},
    parser,
};

fn dominant(vec: Vec<bool>) -> Option<bool> {
    let num_pos = vec.iter().filter(|b| **b).count();
    let num_neg = vec.iter().filter(|b| !**b).count();
    if num_neg == num_pos {
        None
    } else {
        Some(num_neg < num_pos)
    }
}

fn to_number(vec: &[bool]) -> usize {
    vec.iter().fold(0, |s, b| s * 2 + (*b as usize))
}

fn dominant_at(vec: &[Vec<bool>], i: usize, default: bool) -> bool {
    dominant(vec.iter().map(|v| v[i]).collect::<Vec<bool>>()).unwrap_or(default)
}

fn oxygen_g_rate(vec: Vec<Vec<bool>>, i: usize) -> usize {
    if vec.len() == 1 {
        return to_number(&vec[0]);
    }
    let collecting = dominant_at(&vec, i, true);
    let nv: Vec<Vec<bool>> = vec
        .iter()
        .filter(|v| v[i] == collecting)
        .cloned()
        .collect::<Vec<_>>();
    oxygen_g_rate(nv, i + 1)
}

fn co2_s_rate(vec: Vec<Vec<bool>>, i: usize) -> usize {
    if vec.len() == 1 {
        return to_number(&vec[0]);
    }
    let collecting = !dominant_at(&vec, i, true);
    let nv: Vec<Vec<bool>> = vec
        .iter()
        .filter(|v| v[i] == collecting)
        .cloned()
        .collect::<Vec<_>>();
    co2_s_rate(nv, i + 1)
}

#[derive(Clone, Debug, Default)]
pub struct Puzzle {
    line: Vec<Vec<bool>>,
}

impl Puzzle {
    fn gamma_and_epsilon(&self) -> (usize, usize) {
        let len = self.line[0].len();
        let vec = (0..len)
            .map(|i| dominant_at(&self.line, i, true))
            .collect::<Vec<_>>();
        let cev = vec.iter().map(|b| !*b).collect::<Vec<_>>();
        (to_number(&vec), to_number(&cev))
    }
}

#[aoc(2021, 3)]
impl AdventOfCode for Puzzle {
    fn prepare(&mut self, input: &str) -> Result<(), ParseError> {
        for l in input.lines() {
            self.line.push(parser::to_binaries(l)?);
        }
        Ok(())
    }
    fn part1(&mut self) -> usize {
        let (g, e) = self.gamma_and_epsilon();
        g * e
    }
    fn part2(&mut self) -> usize {
        let o = oxygen_g_rate(self.line.clone(), 0);
        let c = co2_s_rate(self.line.clone(), 0);
        o * c
    }
}
