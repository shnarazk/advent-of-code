//! <https://adventofcode.com/2018/day/16>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]

use {
    crate::{
        color,
        framework::{aoc, AdventOfCode, ParseError},
        geometric::neighbors,
        line_parser, regex,
    },
    std::collections::HashMap,
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Vec<usize>>,
    rules: Vec<([usize; 4], [usize; 4], [usize; 4])>,
    input_mode: usize,
    input_buffer: Vec<[usize; 4]>,
    op_map: [usize; 16],
}

#[aoc(2018, 16)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn header(&mut self, input: String) -> Result<String, ParseError> {
        self.input_mode = 0;
        let mut segment = input.split("\n\n\n\n");
        let rules = segment.next().ok_or(ParseError)?;
        for l in rules.split('\n') {
            self.parse_rule(l)?;
        }
        let data = segment.next().ok_or(ParseError)?;
        Ok(data.to_string())
    }
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.line
            .push(line_parser::to_usizes_spliting_with(block, &[' ', ','])?);
        Ok(())
    }
    fn after_insert(&mut self) {
        dbg!(&self.rules.len());
        dbg!(&self.line.len());
        self.determine_op_code();
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut buffer: [usize; 4] = [0; 4];
        let mut count = 0;
        for example in self.rules.iter() {
            let mut success = 0;
            for code in 0..16 {
                let on_note = example.1[0];
                success +=
                    (*execute_as(code, &example.1, &example.0, &mut buffer) == example.2) as usize;
            }
            if 3 <= success {
                count += 1;
            }
        }
        count
    }
    fn part2(&mut self) -> Self::Output2 {
        0
    }
}

impl Puzzle {
    fn parse_rule(&mut self, block: &str) -> Result<(), ParseError> {
        match self.input_mode {
            0 => {
                let parser = regex!(r"^Before: \[([0-9, ]+)\]$");
                let segment = parser.captures(block).ok_or(ParseError)?;
                assert!(self.input_buffer.is_empty());
                let v = line_parser::to_usizes_spliting_with(&segment[1], &[' ', ','])?;
                self.input_buffer.push([v[0], v[1], v[2], v[3]]);
                self.input_mode = 1;
            }
            1 => {
                let v = line_parser::to_usizes_spliting_with(block, &[' ', ','])?;
                self.input_buffer.push([v[0], v[1], v[2], v[3]]);
                self.input_mode = 2;
            }
            2 => {
                let parser = regex!(r"^After:  \[([0-9, ]+)\]$");
                let segment = parser.captures(block).ok_or(ParseError)?;
                let v = line_parser::to_usizes_spliting_with(&segment[1], &[' ', ','])?;
                let t2 = [v[0], v[1], v[2], v[3]];
                let t1 = self.input_buffer.pop().unwrap();
                let t0 = self.input_buffer.pop().unwrap();
                self.rules.push((t0, t1, t2));
                self.input_mode = 3;
            }
            3 => {
                assert!(block.is_empty());
                self.input_mode = 0;
            }
            _ => unreachable!(),
        }
        Ok(())
    }
    fn determine_op_code(&mut self) {
        let mut result: HashMap<(usize, usize), usize> = HashMap::new();
        let mut fail: HashMap<(usize, usize), usize> = HashMap::new();
        let mut tries: HashMap<usize, usize> = HashMap::new();
        let mut buffer: [usize; 4] = [0; 4];
        for example in self.rules.iter() {
            let on_note = example.1[0];
            *tries.entry(on_note).or_insert(0) += 1;
        }
        for code in 0..16 {
            for example in self.rules.iter() {
                let on_note = example.1[0];
                if *execute_as(code, &example.1, &example.0, &mut buffer) == example.2 {
                    *result.entry((on_note, code)).or_insert(0) += 1;
                } else {
                    *fail.entry((on_note, code)).or_insert(0) += 1;
                }
            }
        }
        for on_note in 0..16 {
            print!("{:>3}/{:>2}: ", on_note, tries.get(&on_note).unwrap_or(&0),);
            let mut sum = 0;
            for code in 0..16 {
                let occ = *result.get(&(on_note, code)).unwrap_or(&0);
                let neg = *fail.get(&(on_note, code)).unwrap_or(&0);
                print!(
                    "{}{:>3}/{:>2}{}",
                    if 0 < occ && 0 == neg {
                        color::CYAN
                    } else {
                        color::RESET
                    },
                    occ,
                    neg,
                    color::RESET
                );
                sum += occ;
            }
            println!("  | {:>2}", sum);
        }
    }
}

fn execute_as<'a, 'b>(
    op: usize,
    code: &'a [usize],
    register: &'a [usize; 4],
    out: &'b mut [usize; 4],
) -> &'b mut [usize; 4] {
    macro_rules! reg {
        ($num: expr) => {{
            register[code[$num]]
        }};
    }
    macro_rules! set {
        ($num: expr) => {{
            code[$num]
        }};
    }
    macro_rules! val {
        ($num: expr) => {{
            code[$num]
        }};
    }
    out[..4].copy_from_slice(&register[..4]);
    assert_eq!(&register, &out);
    match op {
        // addr, addi
        0 => out[set!(3)] = reg!(1) + reg!(2),
        1 => out[set!(3)] = reg!(1) + val!(2),
        // mulr, muli
        2 => out[set!(3)] = reg!(1) * reg!(2),
        3 => out[set!(3)] = reg!(1) * val!(2),
        // barr, bari
        4 => out[set!(3)] = reg!(1) & reg!(2),
        5 => out[set!(3)] = reg!(1) & val!(2),
        // borr, bori
        6 => out[set!(3)] = reg!(1) | reg!(2),
        7 => out[set!(3)] = reg!(1) | val!(2),
        // setr, seti
        8 => out[set!(3)] = reg!(1),
        9 => out[set!(3)] = val!(1),
        // gtir, gtri, gtrr
        10 => out[set!(3)] = (val!(1) > reg!(2)) as usize,
        11 => out[set!(3)] = (reg!(1) > val!(2)) as usize,
        12 => out[set!(3)] = (reg!(1) > reg!(2)) as usize,
        // eqir, eqri, eqrr
        13 => out[set!(3)] = (val!(1) == reg!(2)) as usize,
        14 => out[set!(3)] = (reg!(1) == val!(2)) as usize,
        15 => out[set!(3)] = (reg!(1) == reg!(2)) as usize,
        _ => unreachable!(),
    }
    out
}
