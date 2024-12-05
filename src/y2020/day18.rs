//! <https://adventofcode.com/2020/day/18>
use {
    crate::framework::{aoc_at, AdventOfCode, ParseError},
    winnow::{
        branch::alt,
        bytes::{one_of, tag},
        character::dec_int,
        IResult,
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

#[derive(Debug, Default, PartialEq)]
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
            if let Some(e) = Expr::parse1(l) {
                let x = e.traverse(Op::ADD, 0);
                // dbg!((l, x));
                result += x;
            } else {
                panic!("{}", l);
            }
        }
        result
    }
    fn part2(&mut self) -> isize {
        let mut result = 0;
        for l in self.expr.iter() {
            if let Some(e) = Expr::parse2(l) {
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
    fn parse1(input: &str) -> Option<Expr> {
        if let Ok((remain, opr1)) = alt((a_term, a_number))(input.trim_start()) {
            if let Ok((_, (op, opr2))) = a_modifier(remain.trim_start()) {
                Some(Expr::BIOP(op, Box::new(opr1), Box::new(opr2)))
            } else {
                Some(opr1)
            }
        } else {
            None
        }
    }
    fn parse2(input: &str) -> Option<Expr> {
        if let Ok((_, e)) = terms(input.trim_start()) {
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

fn a_number(input: &str) -> IResult<&str, Expr> {
    let (remain, num): (&str, i64) = dec_int(input)?;
    Ok((remain, Expr::NUM(num as isize)))
}

fn an_operator(input: &str) -> IResult<&str, Op> {
    let (remain, op) = one_of("+*-/")(input)?;
    Ok((
        remain,
        match op {
            '+' => Op::ADD,
            '*' => Op::MUL,
            '-' => Op::SUB,
            '/' => Op::DIV,
            _ => panic!(""),
        },
    ))
}

fn a_term(input: &str) -> IResult<&str, Expr> {
    let (remain, _) = tag("(")(input)?;
    let (remain, term) = an_expr(remain)?;
    let (remain, _) = tag(")")(remain)?;
    Ok((remain, Expr::TERM(Box::new(term))))
}

fn an_expr(input: &str) -> IResult<&str, Expr> {
    let (remain, opr1) = alt((a_term, a_number))(input.trim_start())?;
    if let Ok((remain, (op, opr2))) = a_modifier(remain.trim_start()) {
        Ok((
            remain.trim_start(),
            Expr::BIOP(op, Box::new(opr1), Box::new(opr2)),
        ))
    } else {
        Ok((remain, opr1))
    }
}

fn a_modifier(str: &str) -> IResult<&str, (Op, Expr)> {
    let (remain, op) = an_operator(str.trim_start())?;
    let (remain, opr) = an_expr(remain.trim_start())?;
    Ok((remain, (op, opr)))
}

// part 2

fn subexpr(input: &str) -> IResult<&str, Expr> {
    let (remain, _) = tag("(")(input)?;
    let (remain, term) = an_expr2(remain)?;
    let (remain, _) = tag(")")(remain)?;
    Ok((remain, Expr::TERM(Box::new(term))))
}

fn an_factor_operator(input: &str) -> IResult<&str, Op> {
    let (remain, op) = one_of("+-")(input)?;
    Ok((
        remain,
        match op {
            '+' => Op::ADD,
            '-' => Op::SUB,
            _ => unreachable!(""),
        },
    ))
}

fn an_term_operator(input: &str) -> IResult<&str, Op> {
    let (remain, op) = one_of("*/")(input)?;
    Ok((
        remain,
        match op {
            '*' => Op::MUL,
            '/' => Op::DIV,
            _ => unreachable!(""),
        },
    ))
}

fn factors(input: &str) -> IResult<&str, Expr> {
    let (remain, l) = alt((subexpr, a_number))(input.trim_start())?;
    if let Ok((remain, op)) = an_factor_operator(remain.trim_start()) {
        let (remain, r) = factors(remain.trim_start())?;
        Ok((remain, Expr::BIOP(op, Box::new(l), Box::new(r))))
    } else {
        Ok((remain, l))
    }
}

fn terms(input: &str) -> IResult<&str, Expr> {
    let (remain, l) = factors(input.trim_start())?;
    if let Ok((remain, op)) = an_term_operator(remain.trim_start()) {
        let (remain, r) = terms(remain.trim_start())?;
        Ok((remain, Expr::BIOP(op, Box::new(l), Box::new(r))))
    } else {
        Ok((remain, l))
    }
}

fn an_expr2(input: &str) -> IResult<&str, Expr> {
    terms(input.trim_start())
}
