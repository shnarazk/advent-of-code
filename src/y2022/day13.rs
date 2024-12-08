//! <https://adventofcode.com/2022/day/13>
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        parser::parse_usize,
    },
    std::cmp::Ordering,
    winnow::{
        combinator::{alt, separated},
        PResult, Parser,
    },
};

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
enum Expr {
    Num(usize),
    Array(Vec<Expr>),
}

fn parse_expr_num(input: &mut &str) -> PResult<Expr> {
    let a: usize = parse_usize.parse_next(input)?;
    Ok(Expr::Num(a))
}

fn parse_expr(input: &mut &str) -> PResult<Expr> {
    alt((parse_expr_array, parse_expr_num)).parse_next(input)
}

fn parse_expr_array(input: &mut &str) -> PResult<Expr> {
    let _ = "[".parse_next(input)?;
    let e = separated(0.., parse_expr, ",").parse_next(input)?;
    let _ = "]".parse_next(input)?;
    Ok(Expr::Array(e))
}

impl PartialOrd for Expr {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Expr {
    fn cmp(&self, other: &Expr) -> Ordering {
        match (self, other) {
            (Expr::Num(a), Expr::Num(b)) => a.cmp(b),
            (Expr::Array(v1), Expr::Array(v2)) => {
                for i in 0..v1.len().max(v2.len()) {
                    let Some(i1) = v1.get(i) else {
                        return if i == v2.len() {
                            Ordering::Equal
                        } else {
                            Ordering::Less
                        };
                    };
                    let Some(i2) = v2.get(i) else {
                        return Ordering::Greater;
                    };
                    match i1.cmp(i2) {
                        Ordering::Equal => (),
                        other => return other,
                    }
                }
                Ordering::Equal
            }
            (Expr::Num(_), Expr::Array(_)) => Expr::Array(vec![self.clone()]).cmp(other),
            (Expr::Array(_), Expr::Num(_)) => self.cmp(&Expr::Array(vec![other.clone()])),
        }
    }
}

#[derive(Debug, Default, Eq, Hash, PartialEq)]
pub struct Puzzle {
    line: Vec<(Expr, Expr)>,
}

#[aoc(2022, 13)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        let mut lines = block.split('\n').collect::<Vec<_>>();
        self.line.push((
            parse_expr(&mut lines[0]).expect("!!!!"),
            parse_expr(&mut lines[1]).expect("!!!!"),
        ));
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        self.line
            .iter()
            .enumerate()
            .filter(|(_, (a, b))| a.cmp(b) == Ordering::Less)
            .map(|(i, _)| i + 1)
            .sum()
    }
    fn part2(&mut self) -> Self::Output2 {
        let a = Expr::Array(vec![Expr::Array(vec![Expr::Num(2)])]);
        let b = Expr::Array(vec![Expr::Array(vec![Expr::Num(6)])]);
        let mut bag = self
            .line
            .iter()
            .flat_map(|(a, b)| vec![a.clone(), b.clone()])
            .collect::<Vec<_>>();
        bag.push(a.clone());
        bag.push(b.clone());
        bag.sort();
        bag.iter()
            .enumerate()
            .filter(|(_, p)| **p == a || **p == b)
            .map(|(i, _)| i + 1)
            .product()
    }
}
