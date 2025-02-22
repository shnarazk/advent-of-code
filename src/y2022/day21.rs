//! <https://adventofcode.com/2022/day/21>
use {
    crate::{
        framework::{AdventOfCode, ParseError, aoc_at},
        parser::parse_isize,
    },
    std::{cmp::Ordering, collections::HashMap},
    winnow::{
        ModalResult, Parser,
        ascii::{newline, space1},
        combinator::{alt, separated, seq},
        token::one_of,
    },
};
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
#[allow(dead_code)]
enum Expr {
    Num(String, isize),
    Add(String, String, String),
    Sub(String, String, String),
    Mul(String, String, String),
    Div(String, String, String),
    Var,
}

impl Expr {
    fn label(&self) -> &str {
        match self {
            Expr::Num(val, _) => val,
            Expr::Add(val, _, _) => val,
            Expr::Sub(val, _, _) => val,
            Expr::Mul(val, _, _) => val,
            Expr::Div(val, _, _) => val,
            Expr::Var => "X",
        }
    }
    fn arg1(&self) -> &String {
        match self {
            Expr::Num(_, _) => unreachable!(),
            Expr::Add(_, val, _) => val,
            Expr::Sub(_, val, _) => val,
            Expr::Mul(_, val, _) => val,
            Expr::Div(_, val, _) => val,
            Expr::Var => unreachable!(),
        }
    }
    fn arg2(&self) -> &String {
        match self {
            Expr::Num(_, _) => unreachable!(),
            Expr::Add(_, _, val) => val,
            Expr::Sub(_, _, val) => val,
            Expr::Mul(_, _, val) => val,
            Expr::Div(_, _, val) => val,
            Expr::Var => unreachable!(),
        }
    }
    fn eval(&self, v1: isize, v2: isize) -> isize {
        match self {
            Expr::Num(_, _) => unreachable!(),
            Expr::Add(_, _, _) => v1 + v2,
            Expr::Sub(_, _, _) => v1 - v2,
            Expr::Mul(_, _, _) => v1 * v2,
            Expr::Div(_, _, _) => v1 / v2,
            Expr::Var => unreachable!(),
        }
    }
    #[allow(dead_code)]
    fn mnemonic(&self) -> &str {
        match self {
            Expr::Num(_, _) => unreachable!(),
            Expr::Add(_, _, _) => "+",
            Expr::Sub(_, _, _) => "-",
            Expr::Mul(_, _, _) => "*",
            Expr::Div(_, _, _) => "/",
            Expr::Var => unreachable!(),
        }
    }
    #[allow(dead_code)]
    fn build(&self, monkeys: &HashMap<String, Expr>, values: &HashMap<String, isize>) {
        match self {
            Expr::Num(n, _) if n == "humn" => print!("x"),
            Expr::Num(_, val) => print!("{val}"),
            Expr::Add(l, _, _) | Expr::Sub(l, _, _) | Expr::Mul(l, _, _) | Expr::Div(l, _, _)
                if values.contains_key(l) =>
            {
                print!("{}", values.get(l).unwrap());
            }
            Expr::Add(_, l, r) | Expr::Sub(_, l, r) | Expr::Mul(_, l, r) | Expr::Div(_, l, r) => {
                print!("(");
                let lm = monkeys.get(l).unwrap();
                lm.build(monkeys, values);
                print!("{}", self.mnemonic());
                let rm = monkeys.get(r).unwrap();
                rm.build(monkeys, values);
                print!(")");
            }
            Expr::Var => print!("X"),
        }
    }
}

#[derive(Clone, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Expr>,
}

fn parse_id(s: &mut &str) -> ModalResult<String> {
    seq!(
        one_of('a'..='z'),
        one_of('a'..='z'),
        one_of('a'..='z'),
        one_of('a'..='z'),
    )
    .map(|(a, b, c, d)| format!("{a}{b}{c}{d}"))
    .parse_next(s)
}

fn parse_num(s: &mut &str) -> ModalResult<Expr> {
    seq!(
        parse_id,
        _: ": ",
        parse_isize,
    )
    .map(|(dest, num)| Expr::Num(dest, num))
    .parse_next(s)
}

fn parse_term(s: &mut &str) -> ModalResult<Expr> {
    seq!(
        parse_id,
        _: ": ",
        parse_id,
        _: space1,
        one_of(&['+', '-', '*', '/']),
        _: space1,
        parse_id,
    )
    .map(|(dest, src1, opr, src2)| match opr {
        '+' => Expr::Add(dest, src1, src2),
        '-' => Expr::Sub(dest, src1, src2),
        '*' => Expr::Mul(dest, src1, src2),
        '/' => Expr::Div(dest, src1, src2),
        _ => unreachable!(),
    })
    .parse_next(s)
}

fn parse_line(s: &mut &str) -> ModalResult<Expr> {
    alt((parse_num, parse_term)).parse_next(s)
}
fn parse(s: &mut &str) -> ModalResult<Vec<Expr>> {
    separated(1.., parse_line, newline).parse_next(s)
}

#[aoc_at(2022, 21)]
impl AdventOfCode for Puzzle {
    type Output1 = isize;
    type Output2 = isize;
    fn prepare(&mut self, mut input: &str) -> Result<(), ParseError> {
        self.line = parse(&mut input)?;
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut values: HashMap<String, isize> = HashMap::new();
        let mut monkeys: Vec<&Expr> = Vec::new();
        for m in self.line.iter() {
            if let Expr::Num(label, value) = m {
                values.insert(label.to_string(), *value);
            } else {
                monkeys.push(m);
            }
        }
        reduce(&mut monkeys, &mut values);
        *values.get("root").expect("!!")
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut values: HashMap<String, isize> = HashMap::new();
        let mut monkeys: Vec<&Expr> = Vec::new();
        let mut left = "";
        let mut right = "";
        for m in self.line.iter() {
            if let Expr::Num(label, value) = m {
                if "humn" != m.label() {
                    values.insert(label.to_string(), *value);
                }
            } else if "root" == m.label() {
                left = m.arg1();
                right = m.arg2();
            } else {
                monkeys.push(m);
            }
        }
        reduce(&mut monkeys, &mut values);
        let mut upper: isize = isize::MAX / 100;
        let mut lower: isize = -(isize::MAX / 100);
        let mut mid = (upper + lower) / 2;
        let lower_ord = solve(&monkeys, &values, left, right, lower);
        let upper_ord = solve(&monkeys, &values, left, right, upper);
        let mut mid_ord = solve(&monkeys, &values, left, right, mid);
        assert_ne!(lower_ord, upper_ord);
        while mid_ord != Ordering::Equal {
            mid = (upper + lower) / 2;
            mid_ord = solve(&monkeys, &values, left, right, mid);
            if lower_ord == mid_ord {
                lower = mid;
            } else {
                upper = mid;
            }
        }
        mid

        // the first approach
        // let mut monkeys: HashMap<String, Expr> = HashMap::new();
        // monkeys.insert("humn".to_string(), Expr::Var {});
        // for m in self.line.iter() {
        //     if m.label() != "humn" {
        //         monkeys.insert(m.label().to_string(), m.clone());
        //     }
        // }
        // let root = monkeys.get("root").unwrap();
        // let left = root.arg1();
        // let right = root.arg2();
        // dbg!(left, right);

        // let lm = monkeys.get(left).unwrap();
        // lm.build(&monkeys, &values);
        // println!();
        // let rm = monkeys.get(right).unwrap();
        // rm.build(&monkeys, &values);
        // println!();
        // let base = 3_757_272_361_780;
        // for i in 0.. {
        //     let x = base + i;
        //     let d = f(x) - 46779208742730;
        //     dbg!(d, x);
        //     if d <= 0 {
        //         return x;
        //     }
        // }
    }
}

fn reduce(monkeys: &mut Vec<&Expr>, values: &mut HashMap<String, isize>) {
    let mut generated = true;
    while generated {
        generated = false;
        let mut remain = Vec::new();
        while let Some(m) = monkeys.pop() {
            let a1 = m.arg1();
            let a2 = m.arg2();
            let Some(v1) = values.get(a1) else {
                remain.push(m);
                continue;
            };
            let Some(v2) = values.get(a2) else {
                remain.push(m);
                continue;
            };
            let result = m.eval(*v1, *v2);
            values.insert(m.label().to_string(), result);
            generated = true;
        }
        std::mem::swap(monkeys, &mut remain);
    }
}

fn solve(
    monkeys: &[&Expr],
    values: &HashMap<String, isize>,
    left: &str,
    right: &str,
    input: isize,
) -> Ordering {
    let mut m = monkeys.to_owned();
    let mut v = values.clone();
    v.insert("humn".to_string(), input);
    reduce(&mut m, &mut v);
    let lv = v.get(left).unwrap();
    let rv = v.get(right).unwrap();
    lv.cmp(rv)
}
