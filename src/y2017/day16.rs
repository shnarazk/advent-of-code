//! <https://adventofcode.com/2017/day/16>
use crate::framework::{aoc_at, AdventOfCode, ParseError};

#[derive(Clone, Debug, Eq, PartialEq)]
enum Dance {
    Spin(usize),
    Exchange(usize, usize),
    Partner(usize, usize),
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Puzzle {
    line: Vec<Dance>,
}

mod parser {
    use {
        super::*,
        crate::parser::parse_usize,
        winnow::{
            combinator::{alt, separated, seq},
            token::one_of,
            ModalResult, Parser,
        },
    };

    fn parse_line(s: &mut &str) -> ModalResult<Dance> {
        alt((
            seq!(_: "s", parse_usize).map(|(n,)| Dance::Spin(n)),
            seq!(_: "x", parse_usize, _: "/", parse_usize).map(|(a, b)| Dance::Exchange(a, b)),
            seq!(_: "p", one_of(|c: char| c.is_ascii_lowercase()), _: "/", one_of(|c: char| c.is_ascii_lowercase())).map(|(a, b)| Dance::Partner((a as u8 - b'a') as usize, (b as u8 - b'a') as usize)),
        ))
        .parse_next(s)
    }

    pub fn parse(s: &mut &str) -> ModalResult<Vec<Dance>> {
        separated(1.., parse_line, ",").parse_next(s)
    }
}

#[aoc_at(2017, 16)]
impl AdventOfCode for Puzzle {
    type Output1 = String;
    type Output2 = String;
    fn parse(&mut self, input: String) -> Result<String, ParseError> {
        self.line = parser::parse(&mut input.as_str())?;
        Self::parsed()
    }
    fn part1(&mut self) -> Self::Output1 {
        let m = 16;
        let list = self.collapse(
            &self.line.iter().collect::<Vec<_>>(),
            &(0..m).collect::<Vec<usize>>(),
        );
        list.iter()
            .map(|c| ((*c as u8) + b'a') as char)
            .collect::<String>()
    }
    fn part2(&mut self) -> Self::Output2 {
        let m = 16;
        let cycle: usize = (1..=6).product::<usize>();
        let remain: usize = 1_000_000_000_usize % cycle;
        let dance = self.line.iter().collect::<Vec<_>>();
        let mut order1 = (0..m).collect::<Vec<usize>>();
        for _ in 0..remain {
            let mut work1 = self.collapse(&dance, &order1);
            std::mem::swap(&mut order1, &mut work1);
            // dbg!(format!("{order1:?}"));
        }
        order1
            .iter()
            .map(|c| ((*c as u8) + b'a') as char)
            .collect::<String>()
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
