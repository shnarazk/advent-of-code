//! <https://adventofcode.com/2021/day/16>
use crate::{
    framework::{aoc, AdventOfCode, ParseError},
    parser,
};

#[derive(Debug, Default)]
pub struct Puzzle {
    line: Vec<Vec<bool>>,
}

#[aoc(2021, 16)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        if block.chars().all(|c| ['0', '1'].contains(&c)) {
            self.line.push(parser::to_binaries(block)?);
        } else {
            self.line.push(
                block
                    .chars()
                    .flat_map(|c| match c {
                        '0' => vec![false, false, false, false],
                        '1' => vec![false, false, false, true],
                        '2' => vec![false, false, true, false],
                        '3' => vec![false, false, true, true],
                        '4' => vec![false, true, false, false],
                        '5' => vec![false, true, false, true],
                        '6' => vec![false, true, true, false],
                        '7' => vec![false, true, true, true],
                        '8' => vec![true, false, false, false],
                        '9' => vec![true, false, false, true],
                        'A' => vec![true, false, true, false],
                        'B' => vec![true, false, true, true],
                        'C' => vec![true, true, false, false],
                        'D' => vec![true, true, false, true],
                        'E' => vec![true, true, true, false],
                        'F' => vec![true, true, true, true],
                        _ => panic!(),
                    })
                    .collect::<Vec<_>>(),
            );
        }
        Ok(())
    }
    fn end_of_data(&mut self) {
        // dbg!(&self.line);
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut result = 0;
        for l in self.line.iter() {
            // println!("{:?}", to_string(l));
            result = sum_versions(l).0;
        }
        result
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut result = 0;
        for l in self.line.iter() {
            // println!("{:?}", to_string(l));
            result = execute(l).0;
        }
        result
    }
}

fn as_usize(vec: &[bool]) -> usize {
    vec.iter().fold(0, |i, b| i * 2 + (*b as usize))
}

#[allow(dead_code)]
fn to_string(vec: &[bool]) -> String {
    vec.iter()
        .map(|c| if *c { "1" } else { "0" })
        .collect::<Vec<&str>>()
        .join("")
}

fn sum_versions(bits: &[bool]) -> (usize, usize) {
    // let header = (0..level).map(|_| " ").collect::<Vec<&str>>().join("");
    let mut versions: usize = 0;
    if bits.is_empty() || bits.iter().all(|b| !b) {
        return (0, bits.len());
    }
    let version = &bits[..3];
    versions += as_usize(version);
    let type_id = &bits[3..6];
    // println!(
    //     "{}version: {:?}, type: {:?}",
    //     header,
    //     as_usize(version),
    //     as_usize(type_id)
    // );
    let mut i = 6;
    match as_usize(type_id) {
        4 => {
            // println!("{} - literal value packet", header);
            // so skip to ...
            while bits[i] {
                i += 5;
            }
            i += 5;
        }
        _ => {
            // operator packet
            // println!("{} - operator packet: {}", header, to_string(&bits[i..]));
            let length_type_id = as_usize(&bits[i..=i]);
            i += 1;
            if length_type_id == 0 {
                // the next 15 bits are number
                // println!(
                //     "{} - operand is 15 bits: {} => sub packets length = {}",
                //     header,
                //     to_string(&bits[i..i + 15]),
                //     as_usize(&bits[i..i + 15])
                // );
                let goal_i = i + 15 + as_usize(&bits[i..i + 15]);
                i += 15;
                while i < goal_i {
                    // println!("{} - sub packet: {}", header, to_string(&bits[i..]));
                    let (vv, ii) = sum_versions(&bits[i..]);
                    versions += vv;
                    i += ii;
                }
            } else {
                // the next 11 bits are number
                // println!(
                //     "{} - operand is 11 bits: {} means {} sub packets",
                //     header,
                //     to_string(&bits[i..i + 11]),
                //     as_usize(&bits[i..i + 11]),
                // );
                let nsubpacket = as_usize(&bits[i..i + 11]);
                i += 11;
                for _ in 0..nsubpacket {
                    // println!("{} - sub packet: {}", header, to_string(&bits[i..]));
                    let (vv, ii) = sum_versions(&bits[i..]);
                    versions += vv;
                    i += ii;
                }
            }
        }
    }
    // println!("{} - done: {}", header, versions);
    (versions, i)
}

fn execute(bits: &[bool]) -> (usize, usize) {
    // let header = (0..level).map(|_| " ").collect::<Vec<&str>>().join("");
    if bits.is_empty() || bits.iter().all(|b| !b) {
        return (0, bits.len());
    }
    let type_id = &bits[3..6];
    let mut i = 6;
    let result = match as_usize(type_id) {
        4 => {
            // so skip to ...
            let mut digits: Vec<bool> = Vec::new();
            while bits[i] {
                digits.append(&mut bits[i + 1..i + 5].to_vec());
                i += 5;
            }
            digits.append(&mut bits[i + 1..i + 5].to_vec());
            i += 5;
            // println!(
            //     "{} - literal value packet {} => {}",
            //     header,
            //     to_string(&digits),
            //     as_usize(&digits),
            // );
            as_usize(&digits)
        }
        op => {
            // operator packet
            let mut results: Vec<usize> = Vec::new();
            // println!(
            //     "{} - operator {}: {}",
            //     header,
            //     match op {
            //         0 => "sum",
            //         1 => "product",
            //         2 => "minimum",
            //         3 => "maximum",
            //         5 => "greater than",
            //         6 => "less than",
            //         7 => "equal to",
            //         _ => unreachable!(),
            //     },
            //     to_string(&bits[i..])
            // );
            let length_type_id = as_usize(&bits[i..=i]);
            i += 1;
            if length_type_id == 0 {
                // the next 15 bits are number
                // println!("{} - operand is 15 bits: {} => sub packets length = {}",
                //          header,
                //          to_string(&bits[i..i + 15]),
                //          as_usize(&bits[i..i + 15]));
                let goal_i = i + 15 + as_usize(&bits[i..i + 15]);
                i += 15;
                while i < goal_i {
                    // println!("{} - sub packet: {}",
                    //          header,
                    //          to_string(&bits[i..])
                    // );
                    let (rr, ii) = execute(&bits[i..]);
                    results.push(rr);
                    i += ii;
                }
            } else {
                // the next 11 bits are number
                // println!("{} - operand is 11 bits: {} means {} sub packets",
                //          header,
                //          to_string(&bits[i..i + 11]),
                //          as_usize(&bits[i..i + 11]),
                // );
                // as_usize(&bits[5..5 + 15])
                let nsubpacket = as_usize(&bits[i..i + 11]);
                i += 11;
                for _ in 0..nsubpacket {
                    // println!("{} - sub packet: {}", header, to_string(&bits[i..]));
                    let (rr, ii) = execute(&bits[i..]);
                    results.push(rr);
                    i += ii;
                }
            }
            match op {
                0 => results.iter().sum(),
                1 => results.iter().product(),
                2 => *results.iter().min().unwrap(),
                3 => *results.iter().max().unwrap(),
                5 => (results[0] > results[1]) as usize,
                6 => (results[0] < results[1]) as usize,
                7 => (results[0] == results[1]) as usize,
                _ => panic!(),
            }
        }
    };
    // println!("{} - result: {}", header, result);
    (result, i)
}
