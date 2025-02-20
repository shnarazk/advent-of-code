//! <https://adventofcode.com/2018/day/19>

use crate::framework::{aoc, AdventOfCode, ParseError};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Inst>,
    pc_index: usize,
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Inst {
    Addr(usize, usize, usize),
    Addi(usize, usize, usize),
    Mulr(usize, usize, usize),
    Muli(usize, usize, usize),
    Banr(usize, usize, usize),
    Bani(usize, usize, usize),
    Borr(usize, usize, usize),
    Bori(usize, usize, usize),
    Setr(usize, usize, usize),
    Seti(usize, usize, usize),
    Gtir(usize, usize, usize),
    Gtri(usize, usize, usize),
    Gtrr(usize, usize, usize),
    Eqir(usize, usize, usize),
    Eqri(usize, usize, usize),
    Eqrr(usize, usize, usize),
}

impl Inst {
    #[allow(dead_code)]
    fn disassemble(&self, addr: usize, pc_index: usize) -> String {
        let l = |n: &usize| match *n {
            _ if *n == pc_index => "pc",
            0 => "a",
            1 => "b",
            2 => "c",
            3 => "d",
            4 => "e",
            5 => "f",
            _ => unreachable!(),
        };
        let r = |n: &usize| match *n {
            _ if *n == pc_index => format!("{addr}"),
            0 => "a".to_string(),
            1 => "b".to_string(),
            2 => "c".to_string(),
            3 => "d".to_string(),
            4 => "e".to_string(),
            5 => "f".to_string(),
            _ => unreachable!(),
        };
        match self {
            Inst::Addr(o1, o2, o3) => format!("{} = {} + {};", l(o3), r(o1), r(o2)),
            Inst::Addi(o1, o2, o3) => format!("{} = {} + {};", l(o3), r(o1), o2),
            Inst::Mulr(o1, o2, o3) => format!("{} = {} * {};", l(o3), r(o1), r(o2)),
            Inst::Muli(o1, o2, o3) => format!("{} = {} * {};", l(o3), r(o1), o2),
            Inst::Banr(o1, o2, o3) => format!("{} = {} & {};", l(o3), r(o1), r(o2)),
            Inst::Bani(o1, o2, o3) => format!("{} = {} & {};", l(o3), r(o1), o2),
            Inst::Borr(o1, o2, o3) => format!("{} = {} | {};", l(o3), r(o1), r(o2)),
            Inst::Bori(o1, o2, o3) => format!("{} = {} | {};", l(o3), r(o1), o2),
            Inst::Setr(o1, _, o3) => format!("{} = {};", l(o3), r(o1)),
            Inst::Seti(o1, _, o3) => format!("{} = {};", l(o3), o1),
            Inst::Gtir(o1, o2, o3) => format!("{} = ({} > {}) as usize;", l(o3), o1, r(o2)),
            Inst::Gtri(o1, o2, o3) => format!("{} = ({} > {}) as usize;", l(o3), r(o1), o2),
            Inst::Gtrr(o1, o2, o3) => format!("{} = ({} > {}) as usize;", l(o3), r(o1), r(o2)),
            Inst::Eqir(o1, o2, o3) => format!("{} = ({} == {}) as usize;", l(o3), o1, r(o2)),
            Inst::Eqri(o1, o2, o3) => format!("{} = ({} == {}) as usize;", l(o3), r(o1), o2),
            Inst::Eqrr(o1, o2, o3) => format!("{} = ({} == {}) as usize;", l(o3), r(o1), r(o2)),
        }
    }
}

fn execute<'b>(op: &Inst, register: &[usize; 6], out: &'b mut [usize; 6]) -> &'b mut [usize; 6] {
    macro_rules! reg {
        ($num: expr) => {{
            register[*$num]
        }};
    }
    macro_rules! set {
        ($num: expr) => {{
            *$num
        }};
    }
    macro_rules! val {
        ($num: expr) => {{
            *$num
        }};
    }
    out[..6].copy_from_slice(&register[..6]);
    assert_eq!(&register, &out);
    match op {
        // addr, addi
        Inst::Addr(o0, o1, o2) => out[set!(o2)] = reg!(o0) + reg!(o1),
        Inst::Addi(o0, o1, o2) => out[set!(o2)] = reg!(o0) + val!(o1),
        // // mulr, muli
        Inst::Mulr(o0, o1, o2) => out[set!(o2)] = reg!(o0) * reg!(o1),
        Inst::Muli(o0, o1, o2) => out[set!(o2)] = reg!(o0) * val!(o1),
        // // banr, bani
        Inst::Banr(o0, o1, o2) => out[set!(o2)] = reg!(o0) & reg!(o1),
        Inst::Bani(o0, o1, o2) => out[set!(o2)] = reg!(o0) & val!(o1),
        // // borr, bori
        Inst::Borr(o0, o1, o2) => out[set!(o2)] = reg!(o0) | reg!(o1),
        Inst::Bori(o0, o1, o2) => out[set!(o2)] = reg!(o0) | val!(o1),
        // // setr, seti
        Inst::Setr(o0, _, o2) => out[set!(o2)] = reg!(o0),
        Inst::Seti(o0, _, o2) => out[set!(o2)] = val!(o0),
        // // gtir, gtri, gtrr
        Inst::Gtir(o0, o1, o2) => out[set!(o2)] = (val!(o0) > reg!(o1)) as usize,
        Inst::Gtri(o0, o1, o2) => out[set!(o2)] = (reg!(o0) > val!(o1)) as usize,
        Inst::Gtrr(o0, o1, o2) => out[set!(o2)] = (reg!(o0) > reg!(o1)) as usize,
        // // eqir, eqri, eqrr
        Inst::Eqir(o0, o1, o2) => out[set!(o2)] = (val!(o0) == reg!(o1)) as usize,
        Inst::Eqri(o0, o1, o2) => out[set!(o2)] = (reg!(o0) == val!(o1)) as usize,
        Inst::Eqrr(o0, o1, o2) => out[set!(o2)] = (reg!(o0) == reg!(o1)) as usize,
    }
    out
}

mod parser {
    use {
        super::Inst,
        crate::parser::parse_usize,
        winnow::{
            ascii::{newline, space1},
            combinator::{alt, separated, seq},
            ModalResult, Parser,
        },
    };

    fn parse_ip(s: &mut &str) -> ModalResult<usize> {
        seq!(_: "#ip ", parse_usize).map(|(n,)| n).parse_next(s)
    }

    fn parse_inst(s: &mut &str) -> ModalResult<Inst> {
        alt((
            seq!(_: "addr ", parse_usize, _: space1, parse_usize, _: space1, parse_usize)
                .map(|(a, b, c)| Inst::Addr(a, b, c)),
            seq!(_: "addi ", parse_usize, _: space1, parse_usize, _: space1, parse_usize)
                .map(|(a, b, c)| Inst::Addi(a, b, c)),
            seq!(_: "mulr ", parse_usize, _: space1, parse_usize, _: space1, parse_usize)
                .map(|(a, b, c)| Inst::Mulr(a, b, c)),
            seq!(_: "muli ", parse_usize, _: space1, parse_usize, _: space1, parse_usize)
                .map(|(a, b, c)| Inst::Muli(a, b, c)),
            seq!(_: "banr ", parse_usize, _: space1, parse_usize, _: space1, parse_usize)
                .map(|(a, b, c)| Inst::Banr(a, b, c)),
            seq!(_: "bani ", parse_usize, _: space1, parse_usize, _: space1, parse_usize)
                .map(|(a, b, c)| Inst::Bani(a, b, c)),
            seq!(_: "bori ", parse_usize, _: space1, parse_usize, _: space1, parse_usize)
                .map(|(a, b, c)| Inst::Bori(a, b, c)),
            seq!(_: "borr ", parse_usize, _: space1, parse_usize, _: space1, parse_usize)
                .map(|(a, b, c)| Inst::Borr(a, b, c)),
            seq!(_: "setr ", parse_usize, _: space1, parse_usize, _: space1, parse_usize)
                .map(|(a, b, c)| Inst::Setr(a, b, c)),
            seq!(_: "seti ", parse_usize, _: space1, parse_usize, _: space1, parse_usize)
                .map(|(a, b, c)| Inst::Seti(a, b, c)),
            seq!(_: "gtir ", parse_usize, _: space1, parse_usize, _: space1, parse_usize)
                .map(|(a, b, c)| Inst::Gtir(a, b, c)),
            seq!(_: "gtri ", parse_usize, _: space1, parse_usize, _: space1, parse_usize)
                .map(|(a, b, c)| Inst::Gtri(a, b, c)),
            seq!(_: "gtrr ", parse_usize, _: space1, parse_usize, _: space1, parse_usize)
                .map(|(a, b, c)| Inst::Gtrr(a, b, c)),
            seq!(_: "eqir ", parse_usize, _: space1, parse_usize, _: space1, parse_usize)
                .map(|(a, b, c)| Inst::Eqir(a, b, c)),
            seq!(_: "eqri ", parse_usize, _: space1, parse_usize, _: space1, parse_usize)
                .map(|(a, b, c)| Inst::Eqri(a, b, c)),
            seq!(_: "eqrr ", parse_usize, _: space1, parse_usize, _: space1, parse_usize)
                .map(|(a, b, c)| Inst::Eqrr(a, b, c)),
        ))
        .parse_next(s)
    }

    pub fn parse(s: &mut &str) -> ModalResult<(usize, Vec<Inst>)> {
        seq!(parse_ip, _: newline, separated(1.., parse_inst, newline)).parse_next(s)
    }
}

#[aoc(2018, 19)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, mut input: &str) -> Result<(), ParseError> {
        let (ip, insts) = parser::parse(&mut input)?;
        self.pc_index = ip;
        self.line = insts;
        Self::parsed()
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut register: [usize; 6] = [0; 6];
        let mut work: [usize; 6] = [0; 6];
        while let Some(op) = self.line.get(register[self.pc_index]) {
            execute(op, &register, &mut work);
            std::mem::swap(&mut register, &mut work);
            register[self.pc_index] += 1;
        }
        // dbg!(&register);
        register[0]
    }
    fn part2(&mut self) -> Self::Output2 {
        // for (i, c) in self.line.iter().enumerate() {
        //     println!("{:>3}: {}", i, c.disassemble(i, self.pc_index));
        // }
        part2_1()
    }
}

/* Source
  0: pc = 0 + 16;
  1: b = 1;
  2: e = 1;
  3: c = b * e;
  4: c = (c == f) as usize;
  5: pc = c + 5;
  6: pc = 6 + 1;
  7: a = b + a;
  8: e = e + 1;
  9: c = (e > f) as usize;
 10: pc = 10 + c;
 11: pc = 2;
 12: b = b + 1;
 13: c = (b > f) as usize;
 14: pc = c + 14;
 15: pc = 1;
 16: pc = 16 * 16;
 17: f = f + 2;
 18: f = f * f;
 19: f = 19 * f;
 20: f = f * 11;
 21: c = c + 5;
 22: c = c * 22;
 23: c = c + 21;
 24: f = f + c;
 25: pc = 25 + a;
 26: pc = 0;
 27: c = 27;
 28: c = c * 28;
 29: c = 29 + c;
 30: c = 30 * c;
 31: c = c * 14;
 32: c = c * 32;
 33: f = f + c;
 34: a = 0;
 35: pc = 0;
*/

/* Source
   0: pc = 16;
=> 1: b = 1;
=> 2: e = 1;
=> 3: c = b * e;
   4: c = (c == f) as usize;
   5: pc = c + 5;
=> 6: pc = 7;
=> 7: a = b + a;
   8: e = e + 1;
   9: c = (e > f) as usize;
  10: pc = 10 + c;
=>11: pc = 2;
=>12: b = b + 1;
  13: c = (b > f) as usize;
  14: pc = c + 14;
=>15: pc = 1;
=>16: pc = 256;
--------------- initialization
=>17: f = f + 2;  // f = 2
  18: f = f * f;  // f = 4
  19: f = 19 * f; // f = 76;
  20: f = f * 11; // f = 836;
  21: c = c + 5;  // c = 5;
  22: c = c * 22; // c = 110;
  23: c = c + 21; // c = 131;
  24: f = f + c;  // f = 967;
  25: pc = 25 + a;
=>26: pc = 0;
  27: c = 27;     // c = 27;
  28: c = c * 28; // c = 756;
  29: c = 29 + c; // c = 785;
  30: c = 30 * c; // c = 23550;
  31: c = c * 14; // c = 329700;
  32: c = c * 32; // c = 10550400;
  33: f = f + c; // f = 10551367;
  34: a = 0;
  35: pc = 0;
*/

/* Source
[a: 0, b: 1, c: 10550400, d: 1, e: 0, f: 10551367]
while !(b > f) {
  => 2: e = 1;
  => 3: c = b * e;
     4: c = (c == f) as usize;
     5: pc = c + 5;
  => 6: pc = 7;
  => 7: a = b + a;
     8: e = e + 1;
     9: c = (e > f) as usize;
    10: pc = 10 + c;
  =>11: pc = 2;
  =>12: b = b + 1;
}
*/

/* Source
[a: 0, b: 1, c: 10550400, d: 1, e: 0, f: 10551367]
while !(b > f) {
  => 2: e = 1;
  => 3: c = b * e;
     if c == f {
         c = 1;
         a += b;
     } else {
         c = 0;
     }
     8: e += 1;
     if e > f {
         c = 1;
         b += 1;
     } else {
         c = 0;
         goto 3;
     }
}
*/

/* Source
[a: 0, b: 1, c: 10550400, d: 1, e: 1, f: 10551367]
while !(b > f) {
  => 3: c = b * e;
     if c == f {
         a += b;
     }
     8: e += 1;
     if e > f {
         b += 1;
         e = 1;
     } else {
         goto 3;
     }
}
*/

/* Source
[a: 0, b: 1, c: 10550400, d: 1, e: 1, f: 10551367]
while b <= f {
    c = b * e;
    if c == f {
        a += b;
    }
    e += 1;
    if f < e {
        b += 1;
        e = 1;
    }
}
*/

/*
fn part2() -> usize {
    let mut a = 0;
    let mut b = 1;
    let mut e = 1;
    let f = 10551367;
    while b <= f {
        let c = b * e;
        if c == f {
            a += b;
        }
        e += 1;
        if f < e {
            b += 1;
            e = 1;
        }
    }
    a
}
*/

fn part2_1() -> usize {
    let mut a = 0;
    let f = 10551367;
    for i in 1..(f as f64).sqrt() as usize {
        if f % i == 0 {
            a += i;
            a += f / i;
        }
    }
    a
}
