//! <https://adventofcode.com/2018/day/18>
use {
    crate::framework::{AdventOfCode, ParseError, aoc},
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

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Puzzle {
    line: Vec<Vec<Field>>,
    map: HashMap<Dim2, Field>,
}

#[aoc(2018, 18)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, input: &str) -> Result<(), ParseError> {
        self.line = input
            .lines()
            .map(|l| l.chars().map(|c| Field::try_from(c).unwrap()).collect())
            .collect();
        // self.line
        //     .push(input.chars().map(|c| Field::try_from(c).unwrap()).collect());
        // Ok(())
        Self::parsed()
    }
    fn end_of_data(&mut self) {
        for (j, l) in self.line.iter().enumerate() {
            for (i, c) in l.iter().enumerate() {
                self.map.insert((j as isize, i as isize), *c);
            }
        }
    }
    fn part1(&mut self) -> Self::Output1 {
        let height = self.line.len();
        let width = self.line[0].len();
        let mut tmp: HashMap<Dim2, Field> = HashMap::new();
        for _ in 0..10 {
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
        let mut tmp: HashMap<Dim2, Field> = HashMap::new();
        let mut step = 0;
        let limit: usize = 1_000_000_000;
        let check_point = 1000;
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
            step += 1;
            if step == check_point {
                init.clone_from(&self.map);
            } else if check_point < step && step < check_point + 1000 && self.map == init {
                let delta = step - check_point;
                let n = (limit - check_point) / delta;
                step = n * delta + check_point;
                // dbg!(delta, step);
                // dbg!((limit - check_point) / delta);
                self.map.clone_from(&init);
            }
        }
        let n_tree = self.map.values().filter(|f| **f == Field::Tree).count();
        let n_lumb = self.map.values().filter(|f| **f == Field::Lumb).count();
        n_tree * n_lumb
    }
}
