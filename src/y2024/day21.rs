//! <https://adventofcode.com/2024/day/21>
// #![allow(dead_code)]
// #![allow(unused_variables)]
use {
    crate::framework::{aoc, AdventOfCode, ParseError},
    serde::Serialize,
    std::{
        cmp::Ordering,
        collections::{HashMap, HashSet},
        fmt::Write,
        hash::Hash,
    },
    winnow::{
        ascii::newline,
        combinator::{repeat, separated},
        token::one_of,
        PResult, Parser,
    },
};

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
enum Kind1 {
    K0,
    K1,
    K2,
    K3,
    K4,
    K5,
    K6,
    K7,
    K8,
    K9,
    KA,
}

impl std::fmt::Display for Kind1 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Kind1::K0 => '0',
                Kind1::K1 => '1',
                Kind1::K2 => '2',
                Kind1::K3 => '3',
                Kind1::K4 => '4',
                Kind1::K5 => '5',
                Kind1::K6 => '6',
                Kind1::K7 => '7',
                Kind1::K8 => '8',
                Kind1::K9 => '9',
                Kind1::KA => 'A',
            }
        )
    }
}

// impl Kind1 {
//     fn iterator() -> impl Iterator<Item = Kind1> {
//         [
//             Kind1::K0,
//             Kind1::K1,
//             Kind1::K2,
//             Kind1::K3,
//             Kind1::K4,
//             Kind1::K5,
//             Kind1::K6,
//             Kind1::K7,
//             Kind1::K8,
//             Kind1::K6,
//             Kind1::K7,
//             Kind1::K9,
//             Kind1::KA,
//         ]
//         .into_iter()
//     }
// }

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
enum Kind2 {
    U,
    D,
    L,
    R,
    A,
}

impl std::fmt::Display for Kind2 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Kind2::U => '^',
                Kind2::D => 'v',
                Kind2::L => '<',
                Kind2::R => '>',
                Kind2::A => 'A',
            }
        )
    }
}

#[allow(dead_code)]
fn to_string(v: &[Kind2]) -> String {
    v.iter().fold(String::new(), |mut s, k| {
        let _ = write!(s, "{k}");
        s
    })
}

// impl Kind2 {
//     fn iterator() -> impl Iterator<Item = Kind2> {
//         [Kind2::U, Kind2::D, Kind2::L, Kind2::R, Kind2::A].into_iter()
//     }
// }

#[derive(Clone, Debug, Default, Eq, PartialEq, Serialize)]
pub struct Puzzle {
    line: Vec<Vec<Kind1>>,
    lv1: HashMap<(Kind1, Kind1), Kind2>,
    lv2: HashMap<(Kind2, Kind2), Kind2>,
}

fn parse_kind1(s: &mut &str) -> PResult<Kind1> {
    one_of(&['0', '1', '2', '3', '4', '5', '6', '7', '8', '9', '0', 'A'])
        .map(|c| match c {
            '0' => Kind1::K0,
            '1' => Kind1::K1,
            '2' => Kind1::K2,
            '3' => Kind1::K3,
            '4' => Kind1::K4,
            '5' => Kind1::K5,
            '6' => Kind1::K6,
            '7' => Kind1::K7,
            '8' => Kind1::K8,
            '9' => Kind1::K9,
            'A' => Kind1::KA,
            _ => unreachable!(),
        })
        .parse_next(s)
}

fn parse_line(s: &mut &str) -> PResult<Vec<Kind1>> {
    repeat(1.., parse_kind1).parse_next(s)
}

fn parse(s: &mut &str) -> PResult<Vec<Vec<Kind1>>> {
    separated(1.., parse_line, newline).parse_next(s)
}

#[aoc(2024, 21)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, input: String) -> Result<String, ParseError> {
        self.line = parse(&mut input.as_str())?;
        Self::parsed()
    }
    fn end_of_data(&mut self) {
        self.lv1 = [
            ((Kind1::K0, Kind1::K2), Kind2::U),
            ((Kind1::K0, Kind1::KA), Kind2::R),
            ((Kind1::K1, Kind1::K2), Kind2::R),
            ((Kind1::K1, Kind1::K4), Kind2::U),
            ((Kind1::K2, Kind1::K3), Kind2::R),
            ((Kind1::K2, Kind1::K5), Kind2::U),
            ((Kind1::K3, Kind1::K6), Kind2::U),
            ((Kind1::K3, Kind1::KA), Kind2::D),
            ((Kind1::K4, Kind1::K5), Kind2::R),
            ((Kind1::K4, Kind1::K7), Kind2::U),
            ((Kind1::K5, Kind1::K6), Kind2::R),
            ((Kind1::K5, Kind1::K8), Kind2::U),
            ((Kind1::K6, Kind1::K9), Kind2::U),
            ((Kind1::K7, Kind1::K8), Kind2::R),
            ((Kind1::K8, Kind1::K9), Kind2::R),
            // reverse
            ((Kind1::K2, Kind1::K0), Kind2::D),
            ((Kind1::KA, Kind1::K0), Kind2::L),
            ((Kind1::K2, Kind1::K1), Kind2::L),
            ((Kind1::K4, Kind1::K1), Kind2::D),
            ((Kind1::K3, Kind1::K2), Kind2::L),
            ((Kind1::K5, Kind1::K2), Kind2::D),
            ((Kind1::K6, Kind1::K3), Kind2::D),
            ((Kind1::KA, Kind1::K3), Kind2::U),
            ((Kind1::K5, Kind1::K4), Kind2::L),
            ((Kind1::K7, Kind1::K4), Kind2::D),
            ((Kind1::K6, Kind1::K5), Kind2::L),
            ((Kind1::K8, Kind1::K5), Kind2::D),
            ((Kind1::K9, Kind1::K6), Kind2::D),
            ((Kind1::K8, Kind1::K7), Kind2::L),
            ((Kind1::K9, Kind1::K8), Kind2::L),
        ]
        .iter()
        .cloned()
        .collect::<HashMap<_, _>>();
        self.lv2 = [
            ((Kind2::U, Kind2::D), Kind2::D),
            ((Kind2::U, Kind2::A), Kind2::R),
            ((Kind2::D, Kind2::L), Kind2::L),
            ((Kind2::D, Kind2::R), Kind2::R),
            ((Kind2::R, Kind2::A), Kind2::U),
            // reverse
            ((Kind2::D, Kind2::U), Kind2::U),
            ((Kind2::A, Kind2::U), Kind2::L),
            ((Kind2::L, Kind2::D), Kind2::R),
            ((Kind2::R, Kind2::D), Kind2::L),
            ((Kind2::A, Kind2::R), Kind2::D),
        ]
        .iter()
        .cloned()
        .collect::<HashMap<_, _>>();
    }
    fn part1(&mut self) -> Self::Output1 {
        self.line
            .iter()
            .map(|p| {
                let v2 = lift::<Kind1, Kind2>(p, &self.lv1, Kind1::KA, Kind2::A);
                // for v in v2.iter() {
                //     println!("l2: {} ({})", to_string(v), v.len());
                // }
                let v3 = expand(&v2, &self.lv2);
                // for v in v3.iter() {
                //     println!("l3: {} ({})", to_string(v), v.len());
                // }
                let v4 = expand(&v3, &self.lv2);
                // for v in v4.iter() {
                //     println!("{}", to_string(v));
                // }
                v4.iter()
                    .map(|l| {
                        let a = l.len();
                        let b = p
                            .iter()
                            .filter(|k| **k != Kind1::KA)
                            .fold(0, |acc, k| acc * 10 + (*k as usize));
                        (a * b, a, b)
                    })
                    .min()
                    .unwrap_or((0, 0, 0))
            })
            .map(|s| {
                println!("- {:>4} * {:>5} = {:>6}", s.1, s.2, s.0);
                s.0
            })
            .sum::<usize>()
    }
    fn part2(&mut self) -> Self::Output1 {
        self.line
            .iter()
            .map(|p| {
                let mut v2 = lift::<Kind1, Kind2>(p, &self.lv1, Kind1::KA, Kind2::A);
                v2.truncate(1);
                let h2 = v2.iter().map(segmentize).collect::<Vec<_>>();
                dbg!(&h2);
                let v3_ = expand2(&h2, &self.lv2);
                print_shortest(&v3_);
                let v3 = expand(&v2, &self.lv2);
                let _h3 = v3.iter().map(segmentize).collect::<Vec<_>>();
                let v4_ = expand2(&v3_, &self.lv2);
                print_shortest(&v4_);
                let v4 = expand(&v3, &self.lv2);
                let _h4 = v4.iter().map(segmentize).collect::<Vec<_>>();
                v4.iter()
                    .map(|l| {
                        let a = l.len();
                        let b = p
                            .iter()
                            .filter(|k| **k != Kind1::KA)
                            .fold(0, |acc, k| acc * 10 + (*k as usize));
                        (a * b, a, b, l)
                    })
                    .min()
                    .map(|(sum, a, b, l)| {
                        println!("{a} * {b} = {sum}: {}", to_string(l));
                        (sum, a, b)
                    })
                    .unwrap_or((0, 0, 0))
            })
            .map(|s| {
                println!("- {:>4} * {:>5} = {:>6}", s.1, s.2, s.0);
                s.0
            })
            .sum::<usize>()
    } /* fn part2(&mut self) -> Self::Output2 {
          self.line
              .iter()
              .map(|p| {
                  let pack = (
                      p[0],
                      p.windows(2)
                          .map(|p| ((p[0], p[1]), 1))
                          .collect::<HashMap<_, _>>(),
                  );
                  dbg!(&pack);
                  let v2 = lift2::<Kind1, Kind2>(&pack, &self.lv1, Kind1::KA, Kind2::A);
                  // for v in v2.iter() {
                  //     println!("l2: {} ({})", to_string(v), v.len());
                  // }
                  let mut bag = v2;
                  dbg!(&bag);
                  for _i in 0..8 {
                      bag = bag
                          .iter()
                          .flat_map(|p| lift2::<Kind2, Kind2>(p, &self.lv2, Kind2::A, Kind2::A))
                          .collect::<Vec<_>>();
                  }
                  // let l = bag.iter().map(|l| l.len()).collect::<HashSet<_>>();
                  // println!("{:?}", l);
                  bag.iter()
                      .map(|(_, h)| {
                          let a = h.values().sum::<usize>();
                          let b = p
                              .iter()
                              .filter(|k| **k != Kind1::KA)
                              .fold(0, |acc, k| acc * 10 + (*k as usize));
                          (a * b, a, b)
                      })
                      .min()
                      .unwrap_or((0, 0, 0))
              })
              .map(|s| {
                  println!("= {:>4} * {:>5} = {:>6}", s.1, s.2, s.0);
                  s.0
              })
              .sum::<usize>()
      } */
}

fn lift_aux<T1, T2>(dict: &HashMap<(T1, T1), T2>, from: T1, to: T1, post: T2) -> Vec<Vec<T2>>
where
    T1: Copy + Eq,
    T2: Copy + Eq,
{
    let mut to_visit: Vec<(Vec<T1>, Vec<T2>)> = Vec::new();
    to_visit.push((vec![from], Vec::new()));
    let mut _visited: HashSet<T1> = HashSet::new();
    let mut ret: Vec<Vec<T2>> = Vec::new();
    let mut len: usize = usize::MAX;
    while let Some((path, mut lifted_path)) = to_visit.pop() {
        if path.last() == Some(&to) {
            match lifted_path.len().cmp(&len) {
                Ordering::Less => {
                    len = lifted_path.len();
                    lifted_path.push(post);
                    ret = vec![lifted_path];
                }
                Ordering::Equal => {
                    lifted_path.push(post);
                    ret.push(lifted_path);
                }
                Ordering::Greater => {
                    if lifted_path.len() <= len + 1 {
                        lifted_path.push(post);
                        ret.push(lifted_path);
                    }
                }
            }
            continue;
        }
        for (pair, by) in dict.iter() {
            if path.last() == Some(&pair.0) && !path.contains(&pair.1) {
                let mut path1 = path.clone();
                path1.push(pair.1);
                let mut lifted_path1 = lifted_path.clone();
                lifted_path1.push(*by);
                to_visit.push((path1, lifted_path1));
            }
        }
    }
    ret
}

fn lift<T1, T2>(path: &[T1], dict: &HashMap<(T1, T1), T2>, init: T1, post: T2) -> Vec<Vec<T2>>
where
    T1: Copy + std::fmt::Debug + Eq,
    T2: Copy + std::fmt::Debug + Eq,
{
    let mut p = vec![init];
    p.append(&mut path.to_vec());
    p.windows(2).fold(vec![Vec::new()], |acc, segment| {
        let cands = lift_aux(dict, segment[0], segment[1], post);
        acc.iter()
            .flat_map(|pre| {
                cands.iter().map(|c| {
                    let mut path = pre.clone();
                    let mut cc = c.clone();
                    path.append(&mut cc);
                    path
                })
            })
            .collect::<Vec<_>>()
    })
}

fn lift2(
    hash: &HashMap<Vec<Kind2>, usize>,
    dict: &HashMap<(Kind2, Kind2), Kind2>,
) -> Vec<HashMap<Vec<Kind2>, usize>> {
    hash.iter()
        .fold(vec![HashMap::new()], |vec, (segment, _count)| {
            let cands = lift::<Kind2, Kind2>(segment, dict, Kind2::A, Kind2::A);
            cands
                .iter()
                .flat_map(|seq_| {
                    // here
                    let mut seq = vec![Kind2::A];
                    seq.append(&mut seq_.clone());
                    let last = seq.len() - 1;
                    let breaks = seq
                        .iter()
                        .enumerate()
                        .filter(|(n, k)| [0, last].contains(n) || **k == Kind2::A)
                        .map(|(n, _)| n)
                        .collect::<Vec<_>>();
                    let segments = breaks
                        .iter()
                        .enumerate()
                        .filter(|(i, _)| *i % 2 == 0)
                        .map(|(_, n)| *n)
                        .collect::<Vec<_>>()
                        .windows(2)
                        .map(|seg| seq[seg[0] + 1..=seg[1]].to_vec())
                        .collect::<Vec<_>>();

                    // there
                    vec.iter()
                        .map(|hash| {
                            let mut h = hash.clone();
                            for seg in segments.iter() {
                                *h.entry(seg.clone()).or_default() += 1;
                            }
                            h
                        })
                        .collect::<Vec<_>>()
                })
                .collect::<Vec<_>>()
        })
}

fn segmentize(seq_: &Vec<Kind2>) -> HashMap<Vec<Kind2>, usize> {
    let mut seq = vec![Kind2::A];
    seq.append(&mut seq_.to_vec());
    let last = seq.len() - 1;
    let breaks = seq
        .iter()
        .enumerate()
        .filter(|(n, k)| [0, last].contains(n) || **k == Kind2::A)
        .map(|(n, _)| n)
        .collect::<Vec<_>>();
    breaks
        .iter()
        .enumerate()
        .filter(|(i, _)| *i % 2 == 0)
        .map(|(_, n)| *n)
        .collect::<Vec<_>>()
        .windows(2)
        .map(|seg| seq[seg[0] + 1..=seg[1]].to_vec())
        .fold(HashMap::<Vec<Kind2>, usize>::new(), |mut hash, seq| {
            *hash.entry(seq).or_default() += 1;
            hash
        })
}
fn print_shortest(hashes: &[HashMap<Vec<Kind2>, usize>]) {
    let xx = hashes
        .iter()
        .map(|h| (h.iter().map(|(l, n)| l.len() * *n).sum::<usize>(), h))
        .min_by_key(|(count, _)| *count)
        .unwrap();
    println!(
        "{}: {:?}",
        xx.0,
        xx.1.iter()
            .map(|(k, c)| format!("{c}:{}", to_string(k)))
            .collect::<Vec<_>>()
    );
}
fn expand(vec: &[Vec<Kind2>], dict: &HashMap<(Kind2, Kind2), Kind2>) -> Vec<Vec<Kind2>> {
    vec.iter()
        .flat_map(|h| lift::<Kind2, Kind2>(h, dict, Kind2::A, Kind2::A))
        .collect::<Vec<_>>()
}

fn expand2(
    vec: &[HashMap<Vec<Kind2>, usize>],
    dict: &HashMap<(Kind2, Kind2), Kind2>,
) -> Vec<HashMap<Vec<Kind2>, usize>> {
    vec.iter().flat_map(|h| lift2(h, dict)).collect::<Vec<_>>()
}
