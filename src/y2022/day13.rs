//! <https://adventofcode.com/2022/day/13>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::neighbors,
        line_parser, regex,
    },
    nom::{
        branch::alt, bytes::complete::tag, character::complete::digit1, multi::separated_list0,
        IResult,
    },
    std::{cmp::Ordering, collections::HashMap},
};

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
enum Expr {
    Num(usize),
    Array(Vec<Expr>),
}

fn parse_expr_num(input: &str) -> IResult<&str, Expr> {
    let (a, b) = digit1(input)?;
    Ok((a, Expr::Num(b.parse::<usize>().unwrap())))
}

fn parse_expr_array(input: &str) -> IResult<&str, Expr> {
    let (v, _) = tag("[")(input)?;
    let (e, b) = separated_list0(tag(","), parse_expr)(v)?;
    let (r, _) = tag("]")(e)?;
    Ok((r, Expr::Array(b)))
}

fn parse_expr(input: &str) -> IResult<&str, Expr> {
    alt((parse_expr_array, parse_expr_num))(input)
}

fn compare(e1: &Expr, e2: &Expr) -> Ordering {
    // dbg!(e1, e2);
    match (e1, e2) {
        (Expr::Num(a), Expr::Num(b)) => a.cmp(b),
        (Expr::Array(v1), Expr::Array(v2)) => {
            for i in 0..v1.len().max(v2.len()) {
                let Some(i1) = v1.get(i) else { return if i == v2.len() { Ordering::Equal} else { Ordering::Less};};
                let Some(i2) = v2.get(i) else { return Ordering::Greater;};
                match compare(i1, i2) {
                    Ordering::Equal => (),
                    other => return other,
                }
            }
            Ordering::Equal
        }
        (Expr::Num(a), Expr::Array(b)) => compare(&Expr::Array(vec![e1.clone()]), e2),
        (Expr::Array(a), Expr::Num(b)) => compare(e1, &Expr::Array(vec![e2.clone()])),
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
        let mut lines = block.split('\n');
        self.line.push((
            parse_expr(lines.next().unwrap()).expect("!!!!").1,
            parse_expr(lines.next().unwrap()).expect("!!!!").1,
        ));
        Ok(())
    }
    fn after_insert(&mut self) {
        dbg!(&self.line.len());
    }
    fn part1(&mut self) -> Self::Output1 {
        self.line
            .iter()
            .enumerate()
            .filter(|(_, (a, b))| compare(a, b) == Ordering::Less)
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
        bag.sort_by(compare);
        bag.iter()
            .enumerate()
            .filter(|(_, p)| **p == a || **p == b)
            .map(|(i, _)| i + 1)
            .product()
    }
}
