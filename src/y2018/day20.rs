//! <https://adventofcode.com/2018/day/20>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::neighbors,
        line_parser, regex,
    },
    std::{
        cmp::Reverse,
        collections::{BinaryHeap, HashMap, HashSet},
    },
};

type Dim2 = (isize, isize);

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Reg(Vec<u8>);

#[derive(Debug, Eq, Hash, PartialEq)]
enum Rege {
    Segment(Vec<u8>),
    Sequence(Vec<Rege>),
    Branch(Vec<Rege>),
}

impl Rege {
    fn max_path(&self, pathes: &[Vec<u8>]) -> Vec<Vec<u8>> {
        match self {
            Rege::Segment(fragment) => merge(pathes, fragment),
            Rege::Sequence(v) => {
                let mut tmp: Vec<Vec<u8>> = pathes.to_vec();
                for c in v.iter() {
                    tmp = c.max_path(&tmp);
                }
                tmp
            }
            Rege::Branch(v) => v
                .iter()
                .flat_map(|p| p.max_path(pathes))
                .collect::<Vec<_>>(),
        }
    }
    fn render(&self) {
        match self {
            Rege::Segment(v) => print!("{}", v.iter().map(|c| *c as char).collect::<String>()),
            Rege::Sequence(v) => {
                let n = v.len();
                for (i, r) in v.iter().enumerate() {
                    r.render();
                }
            }
            Rege::Branch(v) => {
                let n = v.len();
                print!("(");
                for (i, r) in v.iter().enumerate() {
                    r.render();
                    if i + 1 < n {
                        print!("|");
                    }
                }
                print!(")");
            }
        }
    }
    fn map_to_map(&self, locs: &HashSet<Dim2>, map: &mut HashSet<(Dim2, Dim2)>) -> HashSet<Dim2> {
        match self {
            Rege::Segment(v) => {
                let mut result = HashSet::new();
                for loc in locs.iter() {
                    let mut p = *loc;
                    for c in v.iter() {
                        let mut n = match c {
                            b'N' => (p.0 - 1, p.1),
                            b'E' => (p.0, p.1 + 1),
                            b'S' => (p.0 + 1, p.1),
                            b'W' => (p.0, p.1 - 1),
                            _ => unreachable!(),
                        };
                        map.insert((p, n));
                        std::mem::swap(&mut p, &mut n);
                    }
                    result.insert(p);
                }
                result
            }
            Rege::Sequence(v) => {
                let mut result = HashSet::new();
                for loc in locs.iter() {
                    let mut ls = locs.clone();
                    for k in v.iter() {
                        ls = k.map_to_map(&ls, map);
                    }
                    for l in ls.iter() {
                        result.insert(*l);
                    }
                }
                result
            }
            Rege::Branch(v) => {
                let mut result = HashSet::new();
                for loc in locs.iter() {
                    for p in v.iter().flat_map(|p| p.map_to_map(locs, map)) {
                        result.insert(p);
                    }
                }
                result
            }
        }
    }
}

fn merge(bases: &[Vec<u8>], append: &[u8]) -> Vec<Vec<u8>> {
    if bases.is_empty() {
        return vec![append.to_vec()];
    }
    if append.is_empty() {
        return bases.to_vec();
    }
    let mut result = Vec::new();
    'next: for base in bases.iter() {
        let mut prepend_index = base.len() - 1;
        for (j, c) in append.iter().enumerate() {
            if matches!(
                (base[prepend_index], c),
                (b'N', b'S') | (b'E', b'W') | (b'S', b'N') | (b'W', b'E')
            ) {
                if prepend_index == 0 {
                    if j + 1 < append.len() {
                        result.push(append[j + 1..].to_vec());
                    };
                    continue 'next;
                }
                prepend_index -= 1;
            } else {
                let mut res = base[..=prepend_index].to_vec();
                let mut a = append[j..].to_vec().clone();
                res.append(&mut a);
                result.push(res);
                continue 'next;
            }
        }
        result.push(base[..prepend_index].to_vec());
    }
    result
}

#[test]
fn y2018d20merge1() {
    let a1 = vec![b'a'];
    let a2 = vec![b'a', b'a'];
    let b2 = vec![b'b', b'b'];
    assert_eq!(merge(&[a2], &b2), vec![vec![b'a', b'a', b'b', b'b']]);
    assert_eq!(
        merge(&[a1.clone(), a1], &b2),
        vec![vec![b'a', b'b', b'b'], vec![b'a', b'b', b'b']]
    );
}

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<u8>,
}

fn parse_to_run(string: &[u8], start: usize) -> Result<(Reg, usize), ParseError> {
    let mut i = start;
    while let Some(c) = string.get(i) {
        if *c == b'$' || *c == b')' || *c == b'(' || *c == b'|' {
            break;
        }
        i += 1;
    }
    Ok((Reg(string[start..i].to_vec()), i))
}

fn parse_to_sequence(string: &[u8], start: usize) -> Result<(Rege, usize), ParseError> {
    let mut vec: Vec<Rege> = Vec::new();
    let mut i = start;
    if string.get(start) == Some(&b'(') {
        if let Ok((element, j)) = parse_to_branch(string, i) {
            vec.push(element);
            i = j;
        } else {
        }
    } else if let Ok((element, j)) = parse_to_run(string, i) {
        vec.push(Rege::Segment(element.0));
        i = j;
    } else {
    }
    while let Some(c) = string.get(i) {
        // dbg!(*c as char);
        match c {
            b'|' | b')' | b'$' => {
                break;
            }
            b'(' => {
                if let Ok((element, j)) = parse_to_branch(string, i + 1) {
                    vec.push(element);
                    i = j;
                }
            }
            _ => {
                if let Ok((element, j)) = parse_to_run(string, i) {
                    vec.push(Rege::Segment(element.0));
                    i = j;
                }
            }
        }
    }
    if vec.len() == 1 {
        Ok((vec.pop().unwrap(), i))
    } else {
        Ok((Rege::Sequence(vec), i))
    }
}

fn parse_to_branch(string: &[u8], start: usize) -> Result<(Rege, usize), ParseError> {
    let mut vec: Vec<Rege> = Vec::new();
    let mut i = start;
    if string.get(start) == Some(&b'(') {
        if let Ok((element, j)) = parse_to_branch(string, i) {
            vec.push(element);
            i = j;
        } else {
        }
    } else if let Ok((element, j)) = parse_to_sequence(string, i) {
        vec.push(element);
        i = j;
    } else {
    }
    while let Some(c) = string.get(i) {
        // dbg!(*c as char);
        match c {
            b'(' => {
                if let Ok((element, j)) = parse_to_branch(string, i + 1) {
                    vec.push(element);
                    i = j;
                }
            }
            b'|' => {
                i += 1;
                if string.get(i) == Some(&b'(') {
                    if let Ok((element, j)) = parse_to_branch(string, i) {
                        vec.push(element);
                        i = j;
                    }
                } else if string.get(i) == Some(&b')') {
                    vec.push(Rege::Sequence(Vec::new()));
                } else if let Ok((element, j)) = parse_to_sequence(string, i) {
                    vec.push(element);
                    i = j;
                } else {
                }
            }
            b')' | b'$' => {
                // i += 2;
                break;
            }
            _ => unreachable!(),
        }
    }
    Ok((Rege::Branch(vec), i + 1))
}

#[aoc(2018, 20)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        dbg!(block);
        self.line = block.chars().map(|c| c as u8).collect::<Vec<u8>>();
        Ok(())
    }
    fn after_insert(&mut self) {
        // dbg!(&self.line);
    }
    fn part1(&mut self) -> Self::Output1 {
        self.line.push(b')');
        if let Ok((tree, _)) = parse_to_sequence(&self.line, 1) {
            tree.render();
            println!();
            let start = HashSet::from([(0, 0)]);
            let mut map: HashSet<(Dim2, Dim2)> = HashSet::new();
            let end_points = tree.map_to_map(&start, &mut map);
            let d = distance(&map);
            return *d.values().max().unwrap();
        }
        0
    }
    fn part2(&mut self) -> Self::Output2 {
        0
    }
}

fn distance(map: &HashSet<(Dim2, Dim2)>) -> HashMap<Dim2, usize> {
    let mut dist: HashMap<Dim2, usize> = HashMap::new();
    let mut to_visit: BinaryHeap<Reverse<(usize, Dim2)>> = BinaryHeap::new();
    to_visit.push(Reverse((0, (0, 0))));
    while let Some(Reverse((d, p))) = to_visit.pop() {
        if dist.contains_key(&p) {
            continue;
        }
        dist.insert(p, d);
        for (from, to) in map.iter().filter(|(from, to)| *from == p) {
            if !dist.contains_key(to) {
                to_visit.push(Reverse((d + 1, *to)));
            }
        }
    }
    dist
}
