//! <https://adventofcode.com/2015/day/10>
use crate::framework::{aoc, AdventOfCode, ParseError};

/// Don't work
#[allow(dead_code)]
fn formatter_recursive(vec: &[usize]) -> Vec<usize> {
    if let Some(n) = vec.get(0) {
        let mut nrepeat = 0;
        for (i, x) in vec.iter().enumerate() {
            if x == n {
                nrepeat = i;
            } else {
                break;
            }
        }
        nrepeat += 1;
        let mut v = vec![nrepeat, *n];
        v.append(&mut formatter1(&vec[nrepeat..]));
        v
    } else {
        vec![]
    }
}

fn formatter1(mut vec: &[usize]) -> Vec<usize> {
    let mut v = Vec::new();
    while !vec.is_empty() {
        let n = vec[0];
        let mut nrepeat = 0;
        for (i, x) in vec.iter().enumerate() {
            if *x == n {
                nrepeat = i;
            } else {
                break;
            }
        }
        nrepeat += 1;
        v.push(nrepeat);
        v.push(n);
        vec = &vec[nrepeat..];
    }
    v
}

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Vec<usize>>,
}

#[aoc(2015, 10)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        let mut n = block.parse::<usize>()?;
        let mut vec: Vec<usize> = Vec::new();
        while 0 < n {
            vec.push(n % 10);
            n /= 10;
        }
        vec.reverse();
        self.line.push(vec);
        Ok(())
    }
    fn after_insert(&mut self) {
        // dbg!(&self.line);
    }
    fn part1(&mut self) -> Self::Output1 {
        for v in self.line.iter() {
            let mut n = v.clone();
            for i in 0..40 {
                let result = n
                    .iter()
                    .map(|n| format!("{}", n))
                    .collect::<Vec<String>>()
                    .join("");
                if result.len() < 30 {
                    println!("{}:{}", i, result);
                } else {
                    println!("{}:{}", i, result.len());
                }
                n = formatter1(&n);
            }
            // break;
            let result = n
                .iter()
                .map(|n| format!("{}", n))
                .collect::<Vec<String>>()
                .join("");
            println!(
                "{:?} => {}",
                v.iter()
                    .map(|n| format!("{}", n))
                    .collect::<Vec<String>>()
                    .join(""),
                result.len(),
            );
        }
        0
    }
    fn part2(&mut self) -> Self::Output2 {
        for v in self.line.iter() {
            let mut n = v.clone();
            for i in 0..50 {
                let result = n
                    .iter()
                    .map(|n| format!("{}", n))
                    .collect::<Vec<String>>()
                    .join("");
                if result.len() < 30 {
                    println!("{}:{}", i, result);
                } else {
                    println!("{}:{}", i, result.len());
                }
                n = formatter1(&n);
            }
            // break;
            let result = n
                .iter()
                .map(|n| format!("{}", n))
                .collect::<Vec<String>>()
                .join("");
            println!(
                "{:?} => {}",
                v.iter()
                    .map(|n| format!("{}", n))
                    .collect::<Vec<String>>()
                    .join(""),
                result.len(),
            );
        }
        0
    }
}
