//! <https://adventofcode.com/2023/day/14>
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        math::transpose,
    },
    std::collections::HashMap,
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Vec<usize>>,
}

#[aoc(2023, 14)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.line.push(
            block
                .chars()
                .map(|c| match c {
                    'O' => 1,
                    '#' => 2,
                    _ => 0,
                })
                .collect::<Vec<_>>(),
        );
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        count(&add_force(self.line.clone()))
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut map: HashMap<Vec<Vec<usize>>, usize> = HashMap::new();
        let mut m = self.line.clone();
        map.insert(m.clone(), 0);
        for i in 1.. {
            m = cycle(m);
            if let Some(j) = map.get(&m) {
                let remain = (1000000000 - i) % (i - j);
                for _ in 0..remain {
                    m = cycle(m);
                }
                return count(&m);
            }
            map.insert(m.clone(), i);
        }
        unreachable!()
    }
}

fn add_force(mut mat: Vec<Vec<usize>>) -> Vec<Vec<usize>> {
    let m = transpose(&mat);
    let map = m
        .iter()
        .map(|line| {
            let mut res = Vec::new();
            let mut base = 0;
            for (i, k) in line.iter().enumerate() {
                match *k {
                    1 => {
                        res.push(base);
                        base += 1;
                    }
                    2 => base = i + 1,
                    _ => (),
                }
            }
            res
        })
        .collect::<Vec<_>>();
    for l in mat.iter_mut() {
        for p in l.iter_mut() {
            if *p != 2 {
                *p = 0;
            }
        }
    }
    for (x, l) in map.iter().enumerate() {
        for y in l.iter() {
            mat[*y][x] = 1;
        }
    }
    mat
}

fn rotate_clockwise(m: Vec<Vec<usize>>) -> Vec<Vec<usize>> {
    let h = m.len();
    let mut n = m.clone();
    for (y, l) in n.iter_mut().enumerate() {
        for (x, p) in l.iter_mut().enumerate() {
            *p = m[h - x - 1][y];
        }
    }
    n
}

fn cycle(m: Vec<Vec<usize>>) -> Vec<Vec<usize>> {
    rotate_clockwise(add_force(rotate_clockwise(add_force(rotate_clockwise(
        add_force(rotate_clockwise(add_force(m))),
    )))))
}

fn count(mat: &Vec<Vec<usize>>) -> usize {
    let depth = mat.len();
    let m = transpose(mat);
    m.iter()
        .map(|line| {
            let mut res = Vec::new();
            for (i, k) in line.iter().enumerate() {
                if *k == 1 {
                    res.push(i);
                }
            }
            res.iter().map(|val| depth - val).sum::<usize>()
        })
        .sum::<usize>()
}
