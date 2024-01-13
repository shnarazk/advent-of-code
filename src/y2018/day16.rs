//! <https://adventofcode.com/2018/day/16>

use {
    crate::{
        // color,
        framework::{aoc, AdventOfCode, ParseError},
        line_parser,
        regex,
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
    fn part1(&mut self) -> Self::Output1 {
        let mut buffer: [usize; 4] = [0; 4];
        let mut count = 0;
        for example in self.rules.iter() {
            let mut success = 0;
            for code in 0..16 {
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
        let mut map = [0; 16];
        for (f, t) in self.determine_op_code() {
            map[f] = t;
        }
        let mut register = [0; 4];
        let mut work = [0; 4];
        for op in self.line.iter() {
            execute_as(map[op[0]], op, &register, &mut work);
            std::mem::swap(&mut register, &mut work);
        }
        register[0]
    }
}

impl Puzzle {
    fn parse_rule(&mut self, block: &str) -> Result<(), ParseError> {
        match self.input_mode {
            0 => {
                let parser = regex!(r"^Before: \[([0-9, ]+)\]$");
                let segment = parser.captures(block).ok_or(ParseError)?;
                debug_assert!(self.input_buffer.is_empty());
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
                debug_assert!(block.is_empty());
                self.input_mode = 0;
            }
            _ => unreachable!(),
        }
        Ok(())
    }
    fn determine_op_code(&mut self) -> HashMap<usize, usize> {
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
            // print!("{:>3}/{:>2}: ", on_note, tries.get(&on_note).unwrap_or(&0),);
            // let mut sum = 0;
            for code in 0..16 {
                let _occ = *result.entry((on_note, code)).or_insert(0);
                let _neg = *fail.entry((on_note, code)).or_insert(0);
                // print!(
                //     "{}{:>3}/{:>2}{}",
                //     if 0 < occ && 0 == neg {
                //         color::CYAN
                //     } else {
                //         color::RESET
                //     },
                //     occ,
                //     neg,
                //     color::RESET
                // );
                // sum += occ;
            }
            // println!("  | {:>2}", sum);
        }
        let mut map: HashMap<usize, usize> = HashMap::new();
        'found: while !fail.is_empty() {
            for i in 0..16 {
                if map.values().any(|x| *x == i) {
                    continue;
                }
                let mut zero = 0;
                let mut on_note = 0;
                for (k, v) in fail.iter() {
                    if k.1 != i {
                        continue;
                    }
                    if *v == 0 {
                        on_note = k.0;
                        zero += 1;
                    }
                }
                if 1 == zero {
                    // println!("{} is {}.", on_note, i);
                    map.insert(on_note, i);
                    fail.retain(|k, _| k.0 != on_note);
                    continue 'found;
                }
                // println!("{} has {} possibilities.", i, zero);
            }
            unreachable!();
        }
        debug_assert!(map.len() == 16);
        map
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
    debug_assert_eq!(&register, &out);
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
