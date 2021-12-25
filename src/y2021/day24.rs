//! <https://adventofcode.com/2021/day/24>

use std::collections::HashSet;
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        line_parser,
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
}

#[derive(Debug, Default)]
pub struct Puzzle {
    line: Vec<Inst>,
    jit: Vec<(isize, isize, isize)>,
    z_pool: HashSet<(usize, isize)>,
    best: Vec<usize>,
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
        self.jit = self.build();
        assert!(self.check(vec![9, 9, 9, 1, 1, 9, 8, 3, 9, 4, 9, 5, 8, 4]));
        println!("pass");
        for n in (0..14).rev() {
            print!("{}, ",
                     26usize.pow(
                     self
                     .jit
                     .iter()
                     .take(13 - n)
                     .map(|(k, _, _)| if *k == 26 { -1 } else { 1 })
                     .sum::<isize>() as u32),
            );
        }
        println!();
    }
    fn part1(&mut self) -> Self::Output1 {
        self.search(Vec::new());
        /*
                let mut good: Vec<usize> = Vec::new();
                for z_start in -1000000..1000000 {
                    for w in 1..=9 {
                        let input = vec![w, 8, 9, 9, 9, 9, 9, 9];
                        let mut z = z_start;
                        for (n, pc) in (14-input.len()..14).enumerate() {
                            z = run_with(self.jit[pc].0, self.jit[pc].1, self.jit[pc].2, z, input[n]);
                        }
                        if z == 0 && (good.is_empty() || good < input) {
                            println!("found w={:?}, z_start={}", input, z_start);
                            good = input;
                        }
                    }
                }
        */
        0
    }
    fn part2(&mut self) -> Self::Output2 {
        self.best = [9; 14].to_vec();
        self.search2(Vec::new());
/*
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
            } else if z < 200 {
                println!("{}", z);
            }
            fourteen_digit_number = decl(fourteen_digit_number);
        }
*/
        0
    }
    // fn part2(&mut self) -> Self::Output2 {
    //     0
    // }
}

impl Puzzle {
    fn check(&self, ans: Vec<usize>) -> bool {
        let mut z = 0;
        println!("{:?}", ans);
        print!("{}, ", z);
        for (pc, w) in ans.iter().enumerate() {
            z = run_with(self.jit[pc].0, self.jit[pc].1, self.jit[pc].2, z, *w);
            print!("{}, ", z);
        }
        println!();
        z == 0
    }
    fn dump_z(&self, ans: Vec<usize>) {
        let mut z = 0;
        print!("{}, ", z);
        for (pc, w) in ans.iter().enumerate() {
            z = run_with(self.jit[pc].0, self.jit[pc].1, self.jit[pc].2, z, *w);
            print!("{}, ", z);
        }
        assert_eq!(z, 0);
        println!();
    }
    #[allow(dead_code)]
    fn estimate_z(&self, n: usize) -> isize {
        let mut z = 0;
        for pc in 0..n {
            z = run_with(self.jit[pc].0, self.jit[pc].1, self.jit[pc].2, z, n);
        }
        0
    }
    fn search(&mut self, base: Vec<usize>) {
        // println!("{:?}", base);
        let mut good: Vec<Vec<usize>> = Vec::new();
        let range = self
            .jit
            .iter()
            .take(14 - base.len() - 1)
            .map(|(k, _, _)| if *k == 26 { -1 } else { 1 })
            .sum::<isize>() as u32;
        for z_start in 0..26isize.pow(range) {
            for w in (1..=9).rev() {
                let mut input = base.clone();
                input.insert(0, w);
                let mut z = z_start;
                for (n, pc) in (14 - input.len()..14).enumerate() {
                    z = run_with(self.jit[pc].0, self.jit[pc].1, self.jit[pc].2, z, input[n]);
                }
                if input.len() == 14 {
                    if z == 0 && z_start == 0 {
                        println!("{:?}", &input);
                        self.dump_z(input);
                    }
                    continue;
                }
                if z == 0
                    && !self.z_pool.contains(&(input.len(), z_start))
                    && good.iter().all(|i| *i != input)
                {
                    self.z_pool.insert((input.len(), z_start));
                    good.push(input);
                }
            }
        }
        good.sort();
        while let Some(g) = good.pop() {
            self.search(g);
        }
    }
    fn search2(&mut self, base: Vec<usize>) {
        // println!("{:?}", base);
        let mut good: Vec<Vec<usize>> = Vec::new();
        let range = self
            .jit
            .iter()
            .take(14 - base.len() - 1)
            .map(|(k, _, _)| if *k == 26 { -1 } else { 1 })
            .sum::<isize>() as u32;
        for w in 1..=9 {
            for z_start in 0..=26isize.pow(range) + 26 {
                let mut input = base.clone();
                input.insert(0, w);
                let mut z = z_start;
                for (n, pc) in (14 - input.len()..14).enumerate() {
                    z = run_with(self.jit[pc].0, self.jit[pc].1, self.jit[pc].2, z, input[n]);
                }
                if input.len() == 14 {
                    if z == 0 && z_start == 0 && input < self.best {
                        self.best = input.clone();
                        println!("{:?}", &input);
                        self.dump_z(input);
                    }
                    continue;
                }
                if z == 0 {
                    good.push(input);
                    break;
                }
            }
        }
        good.reverse();
        while let Some(g) = good.pop() {
            self.search2(g);
        }
    }
}

fn run_with(a1: isize, a2: isize, a3: isize, z: isize, wu: usize) -> isize {
    let w: isize = wu as isize;
    let x: isize = (((z % 26) + a2) != w) as isize;
    let y: isize = (w + a3) * x;
    let z: isize = (z / a1) * ((25 * x) + 1);
    z + y
}

#[allow(dead_code)]
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

#[allow(dead_code)]
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
    fn build(&self) -> Vec<(isize, isize, isize)> {
        let mut jit: Vec<(isize, isize, isize)> = Vec::new();
        for (i, l) in self.line.iter().enumerate() {
            if matches!(l, Inst::Inp(_)) {
                /*
                                // print!("{:>3}: ", i);
                                for j in i..i + 18 {
                                    print!(
                                        "{} ",
                                        &match &self.line[j] {
                                            Inst::Inp(c) => format!("In{}", c),
                                            Inst::Add(c, d) => format!(
                                                "Ad{}{}{:?}{}",
                                                c,
                                                if [4, 5, 15].contains(&(j % 18)) {
                                                    RED
                                                } else {
                                                    RESET
                                                },
                                                d,
                                                RESET,
                                            ),
                                            Inst::Mul(c, d) => format!("Mu{}{:?}", c, d),
                                            Inst::Div(c, d) => format!(
                                                "Di{}{}{:?}{}",
                                                c,
                                                if [4, 5, 15].contains(&(j % 18)) {
                                                    RED
                                                } else {
                                                    RESET
                                                },
                                                d,
                                                RESET,
                                            ),
                                            Inst::Mod(c, d) => format!("Mo{}{:?}", c, d),
                                            Inst::Eql(c, d) => format!("Eq{}{:?}", c, d),
                                        }
                                    );
                                }
                                println!();
                */
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
            print!("{:?},", l.0);
        }
        println!();
        jit
    }
    #[allow(dead_code)]
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
            for (_pc, inst) in self.line.iter().enumerate() {
                match inst {
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
