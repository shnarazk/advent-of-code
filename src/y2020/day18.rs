//! <https://adventofcode.com/2020/day/18>
use {
    crate::framework::{aoc_at, AdventOfCode, ParseError},
    winnow::{
        ascii::{dec_int, space0},
        combinator::alt,
        token::one_of,
        PResult, Parser,
    },
};

#[allow(clippy::upper_case_acronyms)]
#[derive(Copy, Clone, Debug, PartialEq)]
enum Op {
    ADD,
    DIV,
    MUL,
    SUB,
}

#[allow(clippy::upper_case_acronyms)]
#[derive(Debug, PartialEq)]
enum Expr {
    BIOP(Op, Box<Expr>, Box<Expr>),
    TERM(Box<Expr>),
    NUM(isize),
}

#[derive(Clone, Debug, Default, PartialEq)]
pub struct Puzzle {
    expr: Vec<String>,
}

#[aoc_at(2020, 18)]
impl AdventOfCode for Puzzle {
    type Output1 = isize;
    type Output2 = isize;
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.expr.push(block.to_string());
        Ok(())
    }
    fn part1(&mut self) -> isize {
        let mut result = 0;
        for l in self.expr.iter() {
            let p = &mut l.trim_start();
            if let Some(e) = Expr::parse1(p) {
                let x = e.traverse(Op::ADD, 0);
                // dbg!((l, x));
                result += x;
            } else {
                panic!("{l} >> {p}");
            }
        }
        result
    }
    fn part2(&mut self) -> isize {
        let mut result = 0;
        for l in self.expr.iter() {
            let p = &mut l.trim_start();
            if let Some(e) = Expr::parse2(p) {
                let x = e.eval();
                // dbg!((l, x));
                result += x;
            } else {
                panic!("{}", l);
            }
        }
        result
    }
}

impl Expr {
    fn parse1(input: &mut &str) -> Option<Expr> {
        let input = &mut input.trim_start();
        if let Ok(opr1) = alt((a_term, a_number)).parse_next(input) {
            if let Ok((op, opr2)) = a_modifier(input) {
                Some(Expr::BIOP(op, Box::new(opr1), Box::new(opr2)))
            } else {
                Some(opr1)
            }
        } else {
            dbg!(input);
            None
        }
    }
    fn parse2(input: &mut &str) -> Option<Expr> {
        if let Ok(e) = terms(input) {
            Some(e)
        } else {
            None
        }
    }
    // for part 1
    fn traverse(&self, op: Op, acum: isize) -> isize {
        match self {
            Expr::BIOP(next_op, l, r) => r.traverse(*next_op, l.traverse(op, acum)),
            Expr::TERM(t) => {
                let n = t.traverse(Op::ADD, 0);
                match op {
                    Op::ADD => acum + n,
                    Op::DIV => acum / n,
                    Op::MUL => acum * n,
                    Op::SUB => acum - n,
                }
            }
            Expr::NUM(n) => match op {
                Op::ADD => acum + n,
                Op::DIV => acum / n,
                Op::MUL => acum * n,
                Op::SUB => acum - n,
            },
        }
    }
    // for part 2
    fn eval(&self) -> isize {
        match self {
            Expr::BIOP(Op::ADD, o1, o2) => o1.eval() + o2.eval(),
            Expr::BIOP(Op::DIV, o1, o2) => o1.eval() / o2.eval(),
            Expr::BIOP(Op::MUL, o1, o2) => o1.eval() * o2.eval(),
            Expr::BIOP(Op::SUB, o1, o2) => o1.eval() - o2.eval(),
            Expr::TERM(e0) => e0.eval(),
            Expr::NUM(n) => *n,
        }
    }
}

fn a_number(input: &mut &str) -> PResult<Expr> {
    let _ = space0(input)?;
    let num: i64 = dec_int.parse_next(input)?;
    Ok(Expr::NUM(num as isize))
}

fn an_operator(input: &mut &str) -> PResult<Op> {
    let _ = space0(input)?;
    let op = one_of(['+', '*', '-', '/']).parse_next(input)?;
    Ok(match op {
        '+' => Op::ADD,
        '*' => Op::MUL,
        '-' => Op::SUB,
        '/' => Op::DIV,
        _ => panic!(""),
    })
}

fn a_term(input: &mut &str) -> PResult<Expr> {
    let _ = space0(input)?;
    let _ = "(".parse_next(input)?;
    let term = an_expr.parse_next(input)?;
    let _ = ")".parse_next(input)?;
    Ok(Expr::TERM(Box::new(term)))
}

fn an_expr(input: &mut &str) -> PResult<Expr> {
    let _ = space0(input)?;
    let opr1 = alt((a_term, a_number)).parse_next(input)?;
    if let Ok((op, opr2)) = a_modifier(input) {
        Ok(Expr::BIOP(op, Box::new(opr1), Box::new(opr2)))
    } else {
        Ok(opr1)
    }
}

fn a_modifier(input: &mut &str) -> PResult<(Op, Expr)> {
    let _ = space0(input)?;
    let op = an_operator(input)?;
    let opr = an_expr(input)?;
    Ok((op, opr))
}

// part 2

fn subexpr(input: &mut &str) -> PResult<Expr> {
    let _ = space0(input)?;
    let _ = "(".parse_next(input)?;
    let term = an_expr2(input)?;
    let _ = ")".parse_next(input)?;
    Ok(Expr::TERM(Box::new(term)))
}

fn an_factor_operator(input: &mut &str) -> PResult<Op> {
    let _ = space0(input)?;
    let op = one_of(['+', '-']).parse_next(input)?;
    Ok(match op {
        '+' => Op::ADD,
        '-' => Op::SUB,
        _ => unreachable!(""),
    })
}

fn an_term_operator(input: &mut &str) -> PResult<Op> {
    let _ = space0(input)?;
    let op = one_of(['*', '/']).parse_next(input)?;
    Ok(match op {
        '*' => Op::MUL,
        '/' => Op::DIV,
        _ => unreachable!(""),
    })
}

fn factors(input: &mut &str) -> PResult<Expr> {
    let _ = space0(input)?;
    let l = alt((subexpr, a_number)).parse_next(input)?;
    if let Ok(op) = an_factor_operator(input) {
        let r = factors(input)?;
        Ok(Expr::BIOP(op, Box::new(l), Box::new(r)))
    } else {
        Ok(l)
    }
}

fn terms(input: &mut &str) -> PResult<Expr> {
    let _ = space0(input)?;
    let l = factors(input)?;
    if let Ok(op) = an_term_operator(input) {
        let r = terms(input)?;
        Ok(Expr::BIOP(op, Box::new(l), Box::new(r)))
    } else {
        Ok(l)
    }
}

fn an_expr2(input: &mut &str) -> PResult<Expr> {
    let _ = space0(input)?;
    terms.parse_next(input)
}
