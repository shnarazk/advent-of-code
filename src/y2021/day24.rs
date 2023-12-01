//! <https://adventofcode.com/2021/day/24>

use {
    crate::{
        color,
        framework::{aoc_at, AdventOfCode, ParseError},
        line_parser, regex,
    },
    std::{cmp::Ordering, collections::HashMap, fmt},
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
    best: Vec<usize>,
    direction: Option<Ordering>,
}

#[aoc_at(2021, 24)]
impl AdventOfCode for Puzzle {
    type Output1 = String;
    type Output2 = String;
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        let inp = regex!(r"^inp ([a-z])$");
        let opr = regex!(r"^([a-z]+) ([a-z]) ([a-z])$");
        let opl = regex!(r"^([a-z]+) ([a-z]) (-?[0-9]+)$");
        if let Some(segment) = inp.captures(block) {
            self.line
                .push(Inst::Inp(segment[1].chars().next().unwrap()));
            return Ok(());
        } else if let Some(segment) = opr.captures(block) {
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
        } else if let Some(segment) = opl.captures(block) {
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
    fn end_of_data(&mut self) {
        self.jit = self.build();
        assert!(self.check(vec![9, 9, 9, 1, 1, 9, 8, 3, 9, 4, 9, 5, 8, 4]));
        println!("pass");
        for n in (0..14).rev() {
            print!(
                "{}, ",
                26usize.pow(
                    self.jit
                        .iter()
                        .take(13 - n)
                        .map(|(k, _, _)| if *k == 26 { -1 } else { 1 })
                        .sum::<isize>() as u32
                ),
            );
        }
        println!();
    }
    fn part1(&mut self) -> Self::Output1 {
        self.direction = Some(Ordering::Greater);
        self.best = [1; 14].to_vec();
        self.search(Vec::new(), 0);
        self.best
            .iter()
            .map(|n| format!("{}", n))
            .collect::<String>()
    }
    fn part2(&mut self) -> Self::Output2 {
        self.direction = Some(Ordering::Less);
        self.best = [9; 14].to_vec();
        self.search(Vec::new(), 0);
        self.best
            .iter()
            .map(|n| format!("{}", n))
            .collect::<String>()
    }
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
    fn dump_z(&self, ans: &[usize]) {
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
    fn search(&mut self, base: Vec<usize>, z_pre: isize) {
        let cand = if self.jit[13 - base.len()].0 == 26 {
            z_pre * 26
        } else {
            z_pre / 26
        };
        // print!("scale {} : ", self.jit[13 - base.len()].0);
        // println!("{}..{} => {}: {:?}", cand, cand + 26, z_pre, base);
        // if base.len() <= 2 {
        //     println!("|| {:?} {}-{} -> {}", base, cand, cand+26, z_pre);
        // }
        for w in 1..=9 {
            for z_start in cand..=cand + 26 {
                let pc = 13 - base.len();
                let z = run_with(self.jit[pc].0, self.jit[pc].1, self.jit[pc].2, z_start, w);
                // if w == 6 && base == vec![8, 4] {
                //     println!("-- {}", z_start);
                // }
                if base.len() == 13 {
                    let mut best = base.clone();
                    best.insert(0, w);
                    if z == z_pre && z_start == 0 && Some(best.cmp(&self.best)) == self.direction {
                        print!(
                            "{}: ",
                            best.iter()
                                .map(|c| (b'0' + *c as u8) as char)
                                .collect::<String>()
                        );
                        self.dump_z(&best);
                        self.best = best;
                    }
                    continue;
                }
                if z == z_pre {
                    let mut input = base.clone();
                    input.insert(0, w);
                    self.search(input, z_start);
                }
            }
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
                // /*
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
                                    color::RED
                                } else {
                                    color::RESET
                                },
                                d,
                                color::RESET,
                            ),
                            Inst::Mul(c, d) => format!("Mu{}{:?}", c, d),
                            Inst::Div(c, d) => format!(
                                "Di{}{}{:?}{}",
                                c,
                                if [4, 5, 15].contains(&(j % 18)) {
                                    color::RED
                                } else {
                                    color::RESET
                                },
                                d,
                                color::RESET,
                            ),
                            Inst::Mod(c, d) => format!("Mo{}{:?}", c, d),
                            Inst::Eql(c, d) => format!("Eq{}{:?}", c, d),
                        }
                    );
                }
                println!();
                // */
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
