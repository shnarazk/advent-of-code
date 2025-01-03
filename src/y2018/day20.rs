//! <https://adventofcode.com/2018/day/20>
use {
    crate::framework::{aoc, AdventOfCode, ParseError},
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
    #[allow(dead_code)]
    fn render(&self) {
        match self {
            Rege::Segment(v) => print!("{}", v.iter().map(|c| *c as char).collect::<String>()),
            Rege::Sequence(v) => {
                for r in v.iter() {
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
                let mut ls = locs.clone();
                for k in v.iter() {
                    ls = k.map_to_map(&ls, map);
                }
                ls
            }
            Rege::Branch(v) => {
                let mut result = HashSet::new();
                for p in v.iter().flat_map(|p| p.map_to_map(locs, map)) {
                    result.insert(p);
                }
                result
            }
        }
    }
}

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
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
        }
    } else if let Ok((element, j)) = parse_to_run(string, i) {
        vec.push(Rege::Segment(element.0));
        i = j;
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
        }
    } else if let Ok((element, j)) = parse_to_sequence(string, i) {
        vec.push(element);
        i = j;
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
        // dbg!(block);
        self.line = block.chars().map(|c| c as u8).collect::<Vec<u8>>();
        Ok(())
    }
    fn end_of_data(&mut self) {
        // dbg!(&self.line);
    }
    fn part1(&mut self) -> Self::Output1 {
        self.line.push(b')');
        if let Ok((tree, _)) = parse_to_sequence(&self.line, 1) {
            // tree.render();
            // println!();
            let start = HashSet::from([(0, 0)]);
            let mut map: HashSet<(Dim2, Dim2)> = HashSet::new();
            let _ = tree.map_to_map(&start, &mut map);
            let d = distance(&map);
            return *d.values().max().unwrap();
        }
        0
    }
    fn part2(&mut self) -> Self::Output2 {
        self.line.push(b')');
        if let Ok((tree, _)) = parse_to_sequence(&self.line, 1) {
            let start = HashSet::from([(0, 0)]);
            let mut map: HashSet<(Dim2, Dim2)> = HashSet::new();
            let _ = tree.map_to_map(&start, &mut map);
            let d = distance(&map);
            return d.values().filter(|n| 1000 <= **n).count();
        }
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
        for (_, to) in map.iter().filter(|(from, _)| *from == p) {
            if !dist.contains_key(to) {
                to_visit.push(Reverse((d + 1, *to)));
            }
        }
    }
    dist
}
