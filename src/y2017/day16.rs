//! <https://adventofcode.com/2017/day/16>
use crate::{
    framework::{aoc, AdventOfCode, ParseError},
    regex,
};

#[derive(Clone, Debug, Eq, PartialEq)]
enum Dance {
    Spin(usize),
    Exchange(usize, usize),
    Partner(usize, usize),
}

impl TryFrom<&str> for Dance {
    type Error = ParseError;
    fn try_from(value: &str) -> Result<Self, Self::Error> {
        fn to_16(val: &str) -> Result<usize, ParseError> {
            if let Some(c) = val.chars().next() {
                Ok(((c as u8) - b'a') as usize)
            } else {
                Err(ParseError)
            }
        }
        let spin = regex!(r"^s(\d+)");
        let exchange = &regex!(r"^x(\d+)/(\d+)$");
        let partner = regex!(r"^p([a-p])/([a-p])$");
        if let Some(segment) = spin.captures(value) {
            Ok(Dance::Spin(segment[1].parse::<usize>()?))
        } else if let Some(segment) = exchange.captures(value) {
            Ok(Dance::Exchange(
                segment[1].parse::<usize>()?,
                segment[2].parse::<usize>()?,
            ))
        } else if let Some(segment) = partner.captures(value) {
            Ok(Dance::Partner(to_16(&segment[1])?, to_16(&segment[2])?))
        } else {
            Err(ParseError)
        }
    }
}

#[derive(Debug, Default, Eq, PartialEq)]
pub struct Puzzle {
    line: Vec<Dance>,
}

#[aoc(2017, 16)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        for seg in block.split(',') {
            self.line.push(Dance::try_from(seg)?);
        }
        Ok(())
    }
    fn end_of_data(&mut self) {
        dbg!(&self.line.len());
    }
    fn part1(&mut self) -> Self::Output1 {
        let m = 16;
        let list = self.collapse(
            &self.line.iter().collect::<Vec<_>>(),
            &(0..m).collect::<Vec<usize>>(),
        );
        println!(
            "{}",
            list.iter()
                .map(|c| ((*c as u8) + b'a') as char)
                .collect::<String>()
        );
        0
    }
    fn part2(&mut self) -> Self::Output2 {
        let m = 16;
        let cycle: usize = (1..=6).product::<usize>();
        let remain: usize = 1_000_000_000_usize % cycle;
        dbg!(cycle, remain);
        let dance = self.line.iter().collect::<Vec<_>>();
        let mut order1 = (0..m).collect::<Vec<usize>>();
        for _ in 0..remain {
            let mut work1 = self.collapse(&dance, &order1);
            std::mem::swap(&mut order1, &mut work1);
            // dbg!(format!("{order1:?}"));
        }
        println!(
            "{}",
            order1
                .iter()
                .map(|c| ((*c as u8) + b'a') as char)
                .collect::<String>()
        );
        0
    }
}

impl Puzzle {
    fn collapse(&self, dance: &[&Dance], init: &[usize]) -> Vec<usize> {
        let m: usize = 16;
        let mut line = init.to_owned();
        let mut work = line.to_owned();
        for d in dance.iter() {
            match d {
                Dance::Spin(n) => {
                    for (i, x) in line.iter().enumerate() {
                        work[(i + n) % m] = *x;
                    }
                    std::mem::swap(&mut line, &mut work);
                }
                Dance::Exchange(x, y) => {
                    line.swap(*x, *y);
                }
                Dance::Partner(x, y) => {
                    let mut pos = (0, 0);
                    for (i, p) in line.iter().enumerate() {
                        match p {
                            _ if p == x => pos.0 = i,
                            _ if p == y => pos.1 = i,
                            _ => (),
                        }
                    }
                    line.swap(pos.0, pos.1);
                }
            }
        }
        line
    }
    #[allow(unused)]
    fn collapse2(&self, m: usize, dance: &[&Dance]) -> Vec<usize> {
        let mut list = (0..m).collect::<Vec<_>>();
        let mut work = list.clone();
        for d in dance.iter() {
            match d {
                Dance::Spin(n) => {
                    for (i, x) in list.iter().enumerate() {
                        work[(i + n) % m] = *x;
                    }
                    std::mem::swap(&mut list, &mut work);
                }
                Dance::Exchange(x, y) => {
                    list.swap(*x, *y);
                }
                Dance::Partner(x, y) => {
                    let mut pos = (0, 0);
                    for (i, p) in list.iter().enumerate() {
                        match p {
                            _ if p == x => pos.0 = i,
                            _ if p == y => pos.1 = i,
                            _ => (),
                        }
                    }
                    list.swap(pos.0, pos.1);
                }
            }
        }
        list
    }
}

// #[test]
// fn check() {
//     use std::collections::HashMap;
//     let m = 8;
//     let order = (0..m).collect::<Vec<usize>>();
//     let puzzle = Puzzle::default();
//     let line = vec![Dance::Spin(1), Dance::Exchange(3, 4), Dance::Partner(4, 1)];
//     let f = puzzle.collapse2(m, &line.iter().collect::<Vec<_>>());
//     let g: Vec<&Dance> = line
//         .iter()
//         .filter(|d| !matches!(d, Dance::Partner(_, _)))
//         .collect::<Vec<_>>();
//     let mut gs: HashMap<usize, Vec<usize>> = HashMap::new();
//     let mut order2 = puzzle.collapse2(m, &g);
//     let mut work = order2.clone();
//     gs.insert(1, work.clone());
//     for p in (1..30).map(|x| 2_usize.pow(x)) {
//         for (i, x) in order2.iter().enumerate() {
//             work[order2[*x]] = i;
//         }
//         dbg!(format!("{p:>10}:{work:?}"));
//         gs.insert(p, work.clone());
//         std::mem::swap(&mut order2, &mut work);
//     }

//     let mut order1 = order.clone();
//     let mut work1 = order.clone();
//     for check in [(1..=m).product(), 2].iter() {
//         dbg!(check);
//         for _ in 0..*check {
//             for (i, x) in order1.iter().enumerate() {
//                 work1[f[*x]] = i;
//             }
//             std::mem::swap(&mut order1, &mut work1);
//             dbg!(format!("{order1:?}"));
//         }
//         dbg!(format!("{order1:?}"));

//         order2 = order.clone();
//         let mut remain = *check;
//         for p in (0..30).map(|n| 2_usize.pow(n)).rev() {
//             if p <= remain {
//                 let ord = gs.get(&p).unwrap();
//                 for (i, x) in order2.iter().enumerate() {
//                     work[ord[*x]] = i;
//                 }
//                 std::mem::swap(&mut order2, &mut work);
//                 remain -= p;
//             }
//         }
//         assert_eq!(order1, order2);
//     }
// }
