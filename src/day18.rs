#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    lazy_static::lazy_static,
    nom::{
        *,
        branch::alt,
        character::complete::*,
        combinator::*,
        IResult,
        multi::many1,
    },
    regex::Regex,
    std::{
        collections::HashMap,
        io::{stdin, Read},
    },
};

#[derive(Copy, Clone, Debug, PartialEq)]
enum Op {
    ADD,
    DIV,
    MUL,
    SUB,
}

#[derive(Debug, PartialEq)]
enum Expr {
    BIOP(Op, Box<Expr>, Box<Expr>),
    TERM(Box<Expr>),
    NUM(i64),
}

impl Expr {
    fn clone_expr(&self) -> Expr {
        match self {
            Expr::BIOP(op, l, r) => Expr::BIOP(*op, Box::new(l.clone_expr()), Box::new(r.clone_expr())),
            Expr::TERM(b) => Expr::TERM(Box::new(b.clone_expr())),
            Expr::NUM(n) => Expr::NUM(*n),
        }
    }
}

fn a_number(input: &str) -> IResult<&str, Expr> {
  map_res(
      recognize(
          many1(
              one_of("0123456789")
          )
      ),
      |out: &str| out.parse::<i64>().map(|a| Expr::NUM(a)))
        (input)
}

fn an_operator(input: &str) -> IResult<&str, Op> {
    map_res(one_of("+*-/"), |c: char| match c {
        '+' => Ok(Op::ADD),
        '*' => Ok(Op::MUL),
        '-' => Ok(Op::SUB),
        '/' => Ok(Op::DIV),
        _ => Err("")
    })(input)
}

fn a_bitree(input: &str) -> IResult<&str, Expr> {
    let (remain, opr1) = an_operand(input)?;
    let (remain, _) = many1(char(' '))(remain)?;
    let (remain, op) = an_operator(remain)?;
    let (remain, _) = many1(char(' '))(remain)?;
    let (remain, opr2) = an_operand(remain)?;
    Ok((remain, Expr::BIOP(op, Box::new(opr1), Box::new(opr2))))
}

fn an_operand(input: &str) -> IResult<&str, Expr> {
    alt((a_term, a_number)) (input)
}

fn a_term(input: &str) -> IResult<&str, Expr> {
    let (remain, _) = char('(')(input)?;
    let (remain, term) = an_expr(remain)?;
    let (remain, _) = char(')')(remain)?;
    Ok((remain, Expr::TERM(Box::new(term))))
}

fn an_expr(input: &str) -> IResult<&str, Expr> {
    let (remain, opr1) = alt((a_term, a_number))(input.trim_start())?;
    if let Ok((remain, (op, opr2))) = a_modifier(remain.trim_start()) {
        Ok((remain.trim_start(), Expr::BIOP(op, Box::new(opr1), Box::new(opr2))))
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
    let (remain, _) = char('(')(input)?;
    let (remain, term) = an_expr2(remain)?;
    let (remain, _) = char(')')(remain)?;
    Ok((remain, Expr::TERM(Box::new(term))))
}


fn an_factor_operator(input: &str) -> IResult<&str, Op> {
    map_res(one_of("+*-/"), |c: char| match c {
//        '*' => Ok(Op::MUL),
//        '/' => Ok(Op::DIV),
        '+' => Ok(Op::ADD),
        '-' => Ok(Op::SUB),
        _ => Err("")
    })(input)
}

fn an_term_operator(input: &str) -> IResult<&str, Op> {
    map_res(one_of("+*-/"), |c: char| match c {
        '*' => Ok(Op::MUL),
        '/' => Ok(Op::DIV),
//        '+' => Ok(Op::ADD),
//        '-' => Ok(Op::SUB),
        _ => Err("")
    })(input)
}

fn factors(input: &str) -> IResult<&str, Expr> {
    let (remain, l) = alt((subexpr, a_number))(input.trim_start())?;
    if let Ok((remain, op)) = an_factor_operator(remain.trim_start()) {
        let (remain, r) = factors(remain.trim_start())?;
        Ok((remain, Expr::BIOP(op, Box::new(l), Box::new(r))))
    } else {
        Ok((remain,l))
    }
}

fn terms(input: &str) -> IResult<&str, Expr> {
    let (remain, l) = factors(input.trim_start())?;
    if let Ok((remain, op)) = an_term_operator(remain.trim_start()) {
        let (remain, r) = terms(remain.trim_start())?;
        Ok((remain, Expr::BIOP(op, Box::new(l), Box::new(r))))
    } else {
        Ok((remain,l))
    }
}

fn an_expr2(input: &str) -> IResult<&str, Expr> {
    terms(input.trim_start())
}

pub fn day18() {
    let mut buf = String::new();
    stdin().read_to_string(&mut buf).expect("wrong");
    dbg!(read(&buf));
}

fn read(str: &str) -> i64 {
    let mut result = 0;
    for l in str.split('\n') {
        if l.is_empty() {
            break;
        }
        // part 1
        /*
        if let Ok(e) = an_expr(l) {
            // dbg!(&e.1);
            let x = traverse(Op::ADD, 0, &e.1);
            dbg!(x);
            result += x;
        } else {
            panic!("{}", l);
        }
         */
        if let Ok(e) = an_expr2(l) {
            let x = eval(&e.1);
            dbg!((l, x));
            result += x;
        } else {
            panic!("{}", l);
        }
    }
    result
}

fn traverse(op: Op, acum: i64, e: &Expr) -> i64 {
    match e {
        Expr::BIOP(next_op, l, r) => {
            traverse(*next_op,
                     traverse(op, acum, &*l),
                     &*r,
            )
        }
        Expr::TERM(t) => {
            let n = traverse(Op::ADD, 0, &t);
            match op {
                Op::ADD => acum + n,
                Op::DIV => acum / n,
                Op::MUL => acum * n,
                Op::SUB => acum - n,
            }
        }
        Expr::NUM(n) => {
            match op {
                Op::ADD => acum + n,
                Op::DIV => acum / n,
                Op::MUL => acum * n,
                Op::SUB => acum - n,
            }
        },
    }
}

fn eval(e: &Expr) -> i64 {
    match e {
        Expr::BIOP(Op::ADD, o1, o2) => eval(o1) + eval(o2),
        Expr::BIOP(Op::DIV, o1, o2) => eval(o1) / eval(o2),
        Expr::BIOP(Op::MUL, o1, o2) => eval(o1) * eval(o2),
        Expr::BIOP(Op::SUB, o1, o2) => eval(o1) - eval(o2),
        Expr::TERM(e0) => eval(e0),
        Expr::NUM(n) => *n,
    }
}

mod test {
    use super::*;
    const TEST1: &str = "\
1 + 2 * 3 + 4 * 5 + 6
1 + (2 * 3) + (4 * (5 + 6))
2 * 3 + (4 * 5)
8 * 3 + 9 + 3 * 4 * 3
(8 * 3 + 9 + 3 * 4 * 3)
5 + (8 * 3 + 9 + 3 * 4 * 3)
5 * 9 * (7 * 3 * 3 + 9 * 3 + (8 + 6 * 4))           
((2 + 4 * 9) * (6 + 9 * 8 + 6) + 6) + 2 + 4 * 2";
    const TEST0: &str = "\
(8 * 3 + 9 + 3 * 4)
";
    #[test]
    fn test1() {
        dbg!(read(TEST1));
        assert_eq!(0, 1);
    }
}
