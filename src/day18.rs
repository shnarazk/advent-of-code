use {
    crate::{Description, ProblemObject, ProblemSolver},
    nom::{branch::alt, character::complete::*, combinator::*, multi::many1, IResult},
};

pub fn day18(part: usize, desc: Description) {
    dbg!(Setting::parse(desc).run(part));
}

#[derive(Copy, Clone, Debug, PartialEq)]
enum Op {
    ADD,
    DIV,
    MUL,
    SUB,
}

impl ProblemObject for String {
    fn parse(line: &str) -> Option<Self> {
        if line.is_empty() {
            None
        } else {
            Some(line.to_string())
        }
    }
}

#[derive(Debug, PartialEq)]
enum Expr {
    BIOP(Op, Box<Expr>, Box<Expr>),
    TERM(Box<Expr>),
    NUM(isize),
}

#[derive(Debug, PartialEq)]
struct Setting {
    expr: Vec<String>,
}

impl ProblemSolver<String, isize, isize> for Setting {
    const DAY: usize = 18;
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, expr: String) {
        self.expr.push(expr);
    }
    fn default() -> Self {
        Setting { expr: Vec::new() }
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
    map_res(recognize(many1(one_of("0123456789"))), |out: &str| {
        out.parse::<isize>().map(|a| Expr::NUM(a))
    })(input)
}

fn an_operator(input: &str) -> IResult<&str, Op> {
    map_res(one_of("+*-/"), |c: char| match c {
        '+' => Ok(Op::ADD),
        '*' => Ok(Op::MUL),
        '-' => Ok(Op::SUB),
        '/' => Ok(Op::DIV),
        _ => Err(""),
    })(input)
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
        _ => Err(""),
    })(input)
}

fn an_term_operator(input: &str) -> IResult<&str, Op> {
    map_res(one_of("+*-/"), |c: char| match c {
        '*' => Ok(Op::MUL),
        '/' => Ok(Op::DIV),
        //        '+' => Ok(Op::ADD),
        //        '-' => Ok(Op::SUB),
        _ => Err(""),
    })(input)
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

#[cfg(test)]
mod test {
    use {
        super::*,
        crate::{Answer, Description},
    };

    #[test]
    fn test1() {
        assert_eq!(
            Setting::parse(Description::TestData("1 + 2 * 3 + 4 * 5 + 6".to_string())).run(1),
            Answer::Part1(71)
        );
        assert_eq!(
            Setting::parse(Description::TestData(
                "1 + (2 * 3) + (4 * (5 + 6))".to_string()
            ))
            .run(1),
            Answer::Part1(51)
        );
        assert_eq!(
            Setting::parse(Description::TestData("2 * 3 + (4 * 5)".to_string())).run(1),
            Answer::Part1(26)
        );
        assert_eq!(
            Setting::parse(Description::TestData(
                "5 + (8 * 3 + 9 + 3 * 4 * 3)".to_string()
            ))
            .run(1),
            Answer::Part1(437)
        );
        assert_eq!(
            Setting::parse(Description::TestData(
                "5 * 9 * (7 * 3 * 3 + 9 * 3 + (8 + 6 * 4))".to_string()
            ))
            .run(1),
            Answer::Part1(12240)
        );
        assert_eq!(
            Setting::parse(Description::TestData(
                "((2 + 4 * 9) * (6 + 9 * 8 + 6) + 6) + 2 + 4 * 2".to_string()
            ))
            .run(1),
            Answer::Part1(13632)
        );
    }
}
