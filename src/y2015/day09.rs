//! <https://adventofcode.com/2015/day/9>
use {
    crate::framework::{aoc, AdventOfCode, ParseError},
    std::collections::{HashMap, HashSet},
};

fn search(
    path: Vec<String>,
    hash: &HashMap<(String, String), usize>,
    weight: usize,
    stop: usize,
) -> usize {
    if stop == 0 {
        // println!("{:?} = {}", path, weight);
        return weight;
    }
    let here: &String = path.last().unwrap();
    let mut new_weight = usize::MAX;
    for ((from, to), dist) in hash.iter() {
        if *from == *here && !path.contains(to) {
            let mut extended = path.clone();
            extended.push(to.to_string());
            let w = search(extended, hash, weight + dist, stop - 1);
            new_weight = new_weight.min(w);
        }
    }
    new_weight
}

fn search2(
    path: Vec<String>,
    hash: &HashMap<(String, String), usize>,
    weight: usize,
    stop: usize,
) -> usize {
    if stop == 0 {
        // println!("{:?} = {}", path, weight);
        return weight;
    }
    let here: &String = path.last().unwrap();
    let mut new_weight = 0;
    for ((from, to), dist) in hash.iter() {
        if *from == *here && !path.contains(to) {
            let mut extended = path.clone();
            extended.push(to.to_string());
            let w = search2(extended, hash, weight + dist, stop - 1);
            new_weight = new_weight.max(w);
        }
    }
    new_weight
}

#[derive(Clone, Debug, Default)]
pub struct Puzzle {
    line: Vec<(String, String, usize)>,
    path: HashMap<(String, String), usize>,
    cities: HashSet<String>,
}

mod parser {
    use {
        crate::parser::parse_usize,
        winnow::{
            ascii::{alpha1, newline},
            combinator::{separated, seq},
            ModalResult, Parser,
        },
    };

    fn parse_line(s: &mut &str) -> ModalResult<(String, String, usize)> {
        seq!(alpha1, _: " to ", alpha1, _: " = ", parse_usize)
            .map(|(a, b, c)| (a.to_string(), b.to_string(), c))
            .parse_next(s)
    }

    pub fn parse(s: &mut &str) -> ModalResult<Vec<(String, String, usize)>> {
        separated(1.., parse_line, newline).parse_next(s)
    }
}

#[aoc(2015, 9)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, input: String) -> Result<String, ParseError> {
        self.line = parser::parse(&mut input.as_str())?;
        Self::parsed()
    }
    fn end_of_data(&mut self) {
        for (c0, c1, d) in self.line.iter() {
            self.path.insert((c0.to_string(), c1.to_string()), *d);
            self.path.insert((c1.to_string(), c0.to_string()), *d);
            self.cities.insert(c0.to_string());
            self.cities.insert(c1.to_string());
        }
        // dbg!(&self.path);
    }
    fn part1(&mut self) -> Self::Output1 {
        self.cities
            .iter()
            .map(|start| {
                search(
                    vec![start.to_string()],
                    &self.path,
                    0,
                    self.cities.len() - 1,
                )
            })
            .min()
            .unwrap()
    }
    fn part2(&mut self) -> Self::Output2 {
        self.cities
            .iter()
            .map(|start| {
                search2(
                    vec![start.to_string()],
                    &self.path,
                    0,
                    self.cities.len() - 1,
                )
            })
            .max()
            .unwrap()
    }
}
