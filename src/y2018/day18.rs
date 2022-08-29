//! <https://adventofcode.com/2018/day/18>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::neighbors,
        line_parser, regex,
    },
    std::collections::HashMap,
};

type Dim2 = (isize, isize);

const DIRS: [Dim2; 8] = [
    (-1, 0),
    (-1, 1),
    (0, 1),
    (1, 1),
    (1, 0),
    (1, -1),
    (0, -1),
    (-1, -1),
];

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Field {
    Open,
    Tree,
    Lumb,
}

impl Field {
    fn transition(&self, n_tree: usize, n_lumb: usize) -> Field {
        match self {
            Field::Open if 3 <= n_tree => Field::Tree,
            Field::Tree if 3 <= n_lumb => Field::Lumb,
            Field::Lumb if 1 <= n_lumb && 1 <= n_tree => Field::Lumb,
            Field::Lumb => Field::Open,
            _ => *self,
        }
    }
}

impl TryFrom<char> for Field {
    type Error = ParseError;
    fn try_from(value: char) -> Result<Self, Self::Error> {
        match value {
            '.' => Ok(Field::Open),
            '|' => Ok(Field::Tree),
            '#' => Ok(Field::Lumb),
            _ => Err(ParseError),
        }
    }
}

#[derive(Debug, Default, Eq, PartialEq)]
pub struct Puzzle {
    line: Vec<Vec<Field>>,
    map: HashMap<Dim2, Field>,
}

#[aoc(2018, 18)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.line
            .push(block.chars().map(|c| Field::try_from(c).unwrap()).collect());
        Ok(())
    }
    fn after_insert(&mut self) {
        for (j, l) in self.line.iter().enumerate() {
            for (i, c) in l.iter().enumerate() {
                self.map.insert((j as isize, i as isize), *c);
            }
        }
        dbg!(&self.map.len());
    }
    fn part1(&mut self) -> Self::Output1 {
        let height = self.line.len();
        let width = self.line[0].len();
        let mut tmp: HashMap<Dim2, Field> = HashMap::new();
        for step in 0..10 {
            tmp.clear();
            for j in 0..height {
                for i in 0..width {
                    let state = self.map.get(&(j as isize, i as isize)).unwrap();
                    let n_tree = DIRS
                        .iter()
                        .map(|d| (j as isize + d.0, i as isize + d.1))
                        .map(|p| *self.map.get(&p).unwrap_or(&Field::Open))
                        .filter(|f| *f == Field::Tree)
                        .count();
                    let n_lumb = DIRS
                        .iter()
                        .map(|d| (j as isize + d.0, i as isize + d.1))
                        .map(|p| *self.map.get(&p).unwrap_or(&Field::Open))
                        .filter(|f| *f == Field::Lumb)
                        .count();
                    tmp.insert((j as isize, i as isize), state.transition(n_tree, n_lumb));
                }
            }
            std::mem::swap(&mut tmp, &mut self.map);
        }
        let n_tree = self.map.values().filter(|f| **f == Field::Tree).count();
        let n_lumb = self.map.values().filter(|f| **f == Field::Lumb).count();
        n_tree * n_lumb
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut init = self.map.clone();
        let height = self.line.len();
        let width = self.line[0].len();
        dbg!(height, width);
        let mut tmp: HashMap<Dim2, Field> = HashMap::new();
        let mut step = 1;
        let limit = 1_000_000_000;
        while step < limit {
            tmp.clear();
            for j in 0..height {
                for i in 0..width {
                    let state = self.map.get(&(j as isize, i as isize)).unwrap();
                    let n_tree = DIRS
                        .iter()
                        .map(|d| (j as isize + d.0, i as isize + d.1))
                        .map(|p| *self.map.get(&p).unwrap_or(&Field::Open))
                        .filter(|f| *f == Field::Tree)
                        .count();
                    let n_lumb = DIRS
                        .iter()
                        .map(|d| (j as isize + d.0, i as isize + d.1))
                        .map(|p| *self.map.get(&p).unwrap_or(&Field::Open))
                        .filter(|f| *f == Field::Lumb)
                        .count();
                    let new_state = state.transition(n_tree, n_lumb);
                    tmp.insert((j as isize, i as isize), new_state);
                }
            }
            std::mem::swap(&mut tmp, &mut self.map);
            if step == 1000 {
                dbg!(self.map.values().filter(|f| **f == Field::Lumb).count());
                init = self.map.clone();
            }
            if 1000 < step && self.map == init {
                let delta = step - 1000;
                dbg!(delta);
                dbg!((limit - 1000) as f64 / delta as f64);
                dbg!(((limit - 1000) / delta) * delta);
                let jump = ((limit - 1000) / delta) * delta + 1000;
                dbg!(jump);
                assert!(limit < jump + delta);
                step = jump;
                self.map = init.clone();
            } else {
                step += 1;
            }
        }
        self.map.values().filter(|f| **f == Field::Lumb).count()
    }
}
