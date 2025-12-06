//! <https://adventofcode.com/2025/day/6>
use {
    crate::{
        array::rotate_anticlockwise,
        framework::{AdventOfCode, ParseError, aoc},
    },
    // rayon::prelude::*,
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Op {
    Add,
    Mul,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Puzzle {
    input: String,
    problem: Vec<Vec<usize>>,
    ops: Vec<Op>,
}

mod parser {
    use {
        super::Op,
        crate::parser::parse_usize,
        winnow::{
            ModalResult, Parser,
            ascii::{newline, space0, space1},
            combinator::{preceded, separated, seq},
            token::one_of,
        },
    };

    fn parse_problem(s: &mut &str) -> ModalResult<Vec<usize>> {
        preceded(space0, separated(1.., parse_usize, space1)).parse_next(s)
    }
    fn parse_problems(s: &mut &str) -> ModalResult<Vec<Vec<usize>>> {
        separated(1.., parse_problem, seq!(space0, newline)).parse_next(s)
    }
    fn parse_op(s: &mut &str) -> ModalResult<Op> {
        one_of(['+', '*'])
            .map(|c: char| if c == '+' { Op::Add } else { Op::Mul })
            .parse_next(s)
    }
    fn parse_ops(s: &mut &str) -> ModalResult<Vec<Op>> {
        preceded(space0, separated(1.., parse_op, space1)).parse_next(s)
    }
    pub fn parse(s: &mut &str) -> ModalResult<(Vec<Vec<usize>>, Vec<Op>)> {
        seq!(parse_problems, newline, parse_ops)
            .parse_next(s)
            .map(|(a, _, b)| (a, b))
    }
}

#[aoc(2025, 6)]
impl AdventOfCode for Puzzle {
    fn prepare(&mut self, mut input: &str) -> Result<(), ParseError> {
        self.input = input.to_string();
        let (p, o) = parser::parse(&mut input).expect("nop");
        self.problem = p;
        self.ops = o;
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        self.ops
            .iter()
            .enumerate()
            .map(|(i, op)| match op {
                Op::Add => self.problem.iter().map(|v| v[i]).fold(0, |acc, x| acc + x),
                Op::Mul => self.problem.iter().map(|v| v[i]).fold(1, |acc, x| acc * x),
            })
            .sum()
    }
    fn part2(&mut self) -> Self::Output2 {
        let s = self
            .input
            .trim()
            .split('\n')
            .map(|s| s.chars().collect::<Vec<_>>())
            .collect::<Vec<_>>();
        let begins = s[s.len() - 1]
            .iter()
            .enumerate()
            .filter(|(_, c)| **c != ' ')
            .map(|(i, _)| i)
            .collect::<Vec<_>>();
        let m = self
            .problem
            .iter()
            .enumerate()
            .map(|(i, l)| {
                l.iter()
                    .enumerate()
                    .map(|(j, n)| {
                        let mut c = 0;
                        while s[i][begins[j] + c] == ' ' {
                            c += 1;
                        }
                        (*n, c as u8)
                    })
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        self.ops
            .iter()
            .enumerate()
            .map(|(i, op)| match op {
                Op::Add => rotate(&m, i).iter().fold(0, |acc, x| acc + x),
                Op::Mul => rotate(&m, i).iter().fold(1, |acc, x| acc * x),
            })
            .sum()
    }
}

fn rotate(m: &[Vec<(usize, u8)>], n: usize) -> Vec<usize> {
    let mut t = m
        .iter()
        .map(|v| (to_vec(v[n].0), v[n].1))
        .collect::<Vec<_>>();
    let d = t.iter().map(|l| l.0.len()).max().unwrap();
    for (l, prefix) in t.iter_mut() {
        for _ in 0..*prefix {
            l.insert(0, 10);
        }
        while l.len() < d {
            l.push(10);
        }
    }
    let u = t.into_iter().map(|p| p.0).collect::<Vec<_>>();
    rotate_anticlockwise(u)
        .iter()
        .map(|l| from_vec(l))
        .collect::<Vec<_>>()
}

fn to_vec(mut n: usize) -> Vec<usize> {
    let mut v: Vec<usize> = Vec::new();
    while n > 0 {
        v.push(n % 10);
        n /= 10;
    }
    v.reverse();
    v
}

fn from_vec(v: &[usize]) -> usize {
    v.into_iter()
        .fold(0, |acc, n| if *n < 10 { acc * 10 + n } else { acc })
}
