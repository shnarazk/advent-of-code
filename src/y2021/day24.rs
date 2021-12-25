//! <https://adventofcode.com/2021/day/24>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]

use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::neighbors,
        line_parser,
        *,
    },
    lazy_static::lazy_static,
    regex::Regex,
    std::collections::HashMap,
    std::fmt,
};

enum Opr {
    Lit(isize),
    Var(char),
}

impl fmt::Debug for Opr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Opr::Lit(n) => write!(f, "{:_>3}", n),
            Opr::Var(c) => write!(f, "_{}", c),
        }
    }
}
#[derive(Debug)]
enum Inst {
    Inp(char),
    Add(char, Opr),
    Mul(char, Opr),
    Div(char, Opr),
    Mod(char, Opr),
    Eql(char, Opr),
    Jit(isize, isize, isize),
}

#[derive(Debug, Default)]
pub struct Puzzle {
    line: Vec<Inst>,
    jit: Vec<(isize, isize, isize)>,
}

#[aoc(2021, 24)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        lazy_static! {
            static ref INP: Regex = Regex::new(r"^inp ([a-z])$").expect("wrong");
            static ref OPR: Regex = Regex::new(r"^([a-z]+) ([a-z]) ([a-z])$").expect("wrong");
            static ref OPL: Regex = Regex::new(r"^([a-z]+) ([a-z]) (-?[0-9]+)$").expect("wrong");
        }
        if let Some(segment) = INP.captures(block) {
            self.line
                .push(Inst::Inp(segment[1].chars().next().unwrap()));
            return Ok(());
        } else if let Some(segment) = OPR.captures(block) {
            let reg1 = segment[2].chars().next().unwrap();
            let reg2 = Opr::Var(segment[3].chars().next().unwrap());
            self.line.push(match &segment[1] {
                "add" => Inst::Add(reg1, reg2),
                "mul" => Inst::Mul(reg1, reg2),
                "div" => Inst::Div(reg1, reg2),
                "mod" => Inst::Mod(reg1, reg2),
                "eql" => Inst::Eql(reg1, reg2),
                _ => unreachable!(),
            });
            return Ok(());
        } else if let Some(segment) = OPL.captures(block) {
            let reg1 = segment[2].chars().next().unwrap();
            let val = Opr::Lit(line_parser::to_isize(&segment[3])?);
            self.line.push(match &segment[1] {
                "add" => Inst::Add(reg1, val),
                "mul" => Inst::Mul(reg1, val),
                "div" => Inst::Div(reg1, val),
                "mod" => Inst::Mod(reg1, val),
                "eql" => Inst::Eql(reg1, val),
                _ => unreachable!(),
            });
            return Ok(());
        }
        Err(ParseError)
    }
    fn after_insert(&mut self) {
        let mut jit: Vec<(isize, isize, isize)> = Vec::new();
        for (i, l) in self.line.iter().enumerate() {
            if matches!(l, Inst::Inp(_)) {
                print!("{:>3}: ", i);
                for j in i..i + 18 {
                    print!(
                        "{} ",
                        &match &self.line[j] {
                            Inst::Inp(c) => format!("In{}", c),
                            Inst::Add(c, d) => format!("Ad{}{}{:?}{}",
                                                       c,
                                                       if [4, 5, 15].contains(&(j % 18)) { RED } else { RESET },
                                                       d,
                                                       RESET,
                            ),
                            Inst::Mul(c, d) => format!("Mu{}{:?}", c, d),
                            Inst::Div(c, d) => format!("Di{}{}{:?}{}", c,
                                                       if [4, 5, 15].contains(&(j % 18)) { RED } else { RESET },
                                                       d,
                                                       RESET,
                            ),
                            Inst::Mod(c, d) => format!("Mo{}{:?}", c, d),
                            Inst::Eql(c, d) => format!("Eq{}{:?}", c, d),
                            _ => unreachable!(),
                        }
                    );
                }
                println!();
                if let Inst::Div(_, Opr::Lit(a1)) = self.line[i + 4] {
                    if let Inst::Add(_, Opr::Lit(a2)) = self.line[i + 5] {
                        if let Inst::Add(_, Opr::Lit(a3)) = self.line[i + 15] {
                            // println!("{:>3},{:>3},{:>3}", a1, a2, a3);
                            jit.push((a1, a2, a3));
                        }
                    }
                }
            }
        }
        for l in jit.iter() {
            println!("{:?}", l);
        }
        self.jit = jit;
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut fourteen_digit_number = Some([9usize; 14].to_vec());
        while let Some(ref n) = fourteen_digit_number {
            let mut z: isize = 0;
            println!("{:?}", n);
            for (i, w) in n.to_vec().iter().enumerate() {
                z = run_with(self.jit[i].0, self.jit[i].1, self.jit[i].2, z, *w);
            }
            if z == 0 {
                println!("{:?}", n);
                return 0;
            } else if z < 200 { println!("{}", z); }
            fourteen_digit_number = decl(fourteen_digit_number);
        }
        0
    }
    fn part2(&mut self) -> Self::Output2 {
        0
    }
}

fn run_with(a1: isize, a2: isize, a3: isize, z: isize, wu: usize) -> isize {
    let w: isize = wu as isize;
    let x: isize = (((z % 26) + a2) != w) as isize;
    let y: isize = (w + a3) * x;
    let z: isize = (z / a1) * ((25 * x) + 1);
    z + y
}

#[derive(Debug, Default, Eq, PartialEq)]
struct Cpu {
    reg: [isize; 3],
}

fn decl(vec: Option<Vec<usize>>) -> Option<Vec<usize>> {
    let v = vec.unwrap();
    let mut nv = v.clone();
    for i in (0..v.len()).rev() {
        if v[i] == 1 {
            nv[i] = 9;
        } else {
            nv[i] -= 1;
            return Some(nv);
        }
    }
    None
}

fn incl(vec: Option<Vec<usize>>) -> Option<Vec<usize>> {
    let v = vec.unwrap();
    let mut nv = v.clone();
    for i in (0..v.len()).rev() {
        if v[i] == 9 {
            nv[i] = 1;
        } else {
            nv[i] += 1;
            return Some(nv);
        }
    }
    None
}

impl Puzzle {
        fn old_part1(&mut self) -> isize {
        let mut cpu: HashMap<char, isize> = HashMap::new();
        let mut fourteen_digit_number = Some([1usize; 14].to_vec());
        // let mut fourteen_digit_number = Some([9usize; 5].to_vec());
        while let Some(ref n) = fourteen_digit_number {
            cpu.insert('w', 0);
            cpu.insert('x', 0);
            cpu.insert('y', 0);
            cpu.insert('z', 0);
            let mut input = n.to_vec();
            // println!("{:?}", input);
            let input2 = input.clone();
            input.reverse();
            let mut z: isize = 0;
            for (pc, inst) in self.line.iter().enumerate() {
                match inst {
                    Inst::Jit(a1, a2, a3) => {
                        let w: isize = input.pop().unwrap() as isize;
                        // z = z * (25 * (z % 26) + a2 != w) + a1 + (w + a3) * x
                        let z: &mut isize = cpu.entry('z').or_default();
                        let tmp: isize = ((*z % 26) + a2 != w) as isize;
                        *z = (*z / a1) * ((25 * tmp) + 1) + (w + a3) * tmp;
                    }
                    Inst::Inp(r1) => {
                        if let Some(index) = 13_usize.checked_sub(input.len()) {
                            let (a1, a2, a3) = self.jit[index];
                            dbg!((a1, a2, a3, z));
                            z = run_with(a1, a2, a3, z, input2[index]);
                            assert_eq!(z, *cpu.get(&'z').unwrap());
                        }
                        // println!("{},{},{},{}",
                        //          cpu.get(&'w').unwrap(),
                        //          cpu.get(&'x').unwrap(),
                        //          cpu.get(&'y').unwrap(),
                        //          cpu.get(&'z').unwrap(),
                        // );
                        // dbg!(&cpu);
                        *cpu.entry(*r1).or_default() = input.pop().unwrap() as isize;
                    }
                    Inst::Add(r1, Opr::Lit(n)) => {
                        *cpu.entry(*r1).or_default() += n;
                    }
                    Inst::Add(r1, Opr::Var(r2)) => {
                        let v = *cpu.get(r2).unwrap();
                        *cpu.entry(*r1).or_default() += v;
                    }
                    Inst::Mul(r1, Opr::Lit(n)) => {
                        *cpu.entry(*r1).or_default() *= n;
                    }
                    Inst::Mul(r1, Opr::Var(r2)) => {
                        let v = *cpu.get(r2).unwrap();
                        *cpu.entry(*r1).or_default() *= v;
                    }
                    Inst::Div(r1, Opr::Lit(n)) => {
                        *cpu.entry(*r1).or_default() /= n;
                    }
                    Inst::Div(r1, Opr::Var(r2)) => {
                        let v = *cpu.get(r2).unwrap();
                        *cpu.entry(*r1).or_default() /= v;
                    }
                    Inst::Mod(r1, Opr::Lit(n)) => {
                        *cpu.entry(*r1).or_default() %= n;
                    }
                    Inst::Mod(r1, Opr::Var(r2)) => {
                        let v = *cpu.get(r2).unwrap();
                        *cpu.entry(*r1).or_default() %= v;
                    }
                    Inst::Eql(r1, Opr::Lit(n)) => {
                        *cpu.entry(*r1).or_default() =
                            if *cpu.get(r1).unwrap() == *n { 1 } else { 0 };
                    }
                    Inst::Eql(r1, Opr::Var(r2)) => {
                        *cpu.entry(*r1).or_default() =
                            if *cpu.get(r1).unwrap() == *cpu.get(r2).unwrap() {
                                1
                            } else {
                                0
                            };
                    }
                }
            }
/*
            let mut z = 0;
            for (i, w) in input2.iter().enumerate() {
                if let Inst::Jit(a1, a2, a3) = self.jit[i] {
                    dbg!((a1, a2, a3, z));
                    z = run_with(a1, a2, a3, z, *w);
                }
            }
            assert_eq!(z, *cpu.get(&'z').unwrap());
*/
            if *cpu.get(&'z').unwrap() == 0 {
                dbg!(n);
                return 0;
            } else if *cpu.get(&'z').unwrap() < 200 {
                println!("{}", cpu.get(&'z').unwrap());
            }
            fourteen_digit_number = incl(fourteen_digit_number);
        }
        0
    }
}
