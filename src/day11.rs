#![allow(dead_code)]
#![allow(unused_variables)]
use std::io::{self, Read};

#[derive(Debug, PartialEq)]
struct World {
    data: Vec<Vec<char>>,
    size: usize,
}

impl World {
    fn from(data: Vec<Vec<char>>) -> Self {
        // assert_eq!(data.len(), data[0].len());
        let size = data.len();
        World { data, size }
    }
    fn at(&self, i: usize, j: usize) -> char {
        self.data[i][j]
    }
    fn neighbors(&self, i: usize, j: usize) -> Vec<char> {
        let mut vec: Vec<char> = Vec::new();
        for oi in &[-1, 0, 1] {
            if (0 == i && *oi == -1) || (i == self.data.len() - 1 && *oi == 1) {
                continue;
            }
            for oj in &[-1, 0, 1] {
                if (0 == j && *oj == -1) || (j == self.data[0].len() - 1 && *oj == 1) {
                    continue;
                }
                if *oi == 0 && *oj == 0 {
                    continue;
                }
                vec.push(self.data[(i as isize + oi) as usize][((j as isize) + oj) as usize]);
            }
        }
        vec
    }
    fn with_offset(&self, i: usize, j: usize, oi: isize, oj: isize) -> Option<char> {
        let ii: isize = i as isize + oi;
        let jj: isize = j as isize + oj;
        if ii < 0 || self.data.len() as isize <= ii || jj < 0 || self.data[0].len() as isize <= jj {
            return None;
        }
        Some(self.at(ii as usize, jj as usize))
    }
    fn num_occupied(&self) -> usize {
        self.data
            .iter()
            .map(|v| v.iter().filter(|c| **c == '#').count())
            .sum()
    }
    fn num_occupied_around(&self, i: usize, j: usize) -> usize {
        self.neighbors(i, j).iter().filter(|c| **c == '#').count()
    }
    fn find_around_through(
        &self,
        c: char,
        blockers: &[char],
        bi: usize,
        bj: usize,
        ii: isize,
        jj: isize,
    ) -> bool {
        let mut scale: isize = 1;
        while let Some(v) = self.with_offset(bi, bj, ii * scale, jj * scale) {
            if v == c {
                return true;
            }
            if blockers.contains(&v) {
                return false;
            }
            scale += 1;
        }
        false
    }
    fn num_occupied_around_through(&self, i: usize, j: usize) -> usize {
        let dirs = [
            (-1, 0),
            (-1, 1),
            (0, 1),
            (1, 1),
            (1, 0),
            (1, -1),
            (0, -1),
            (-1, -1),
        ];
        dirs.iter()
            .filter(|(oi, oj)| self.find_around_through('#', &['L'], i, j, *oi, *oj))
            .count()
    }

    fn next(&mut self) -> Self {
        let mut v: Vec<Vec<char>> = self.data.clone();
        for i in 0..self.data.len() {
            for j in 0..self.data[0].len() {
                let no = self.num_occupied_around(i, j);
                match self.at(i, j) {
                    'L' if no == 0 => v[i][j] = '#',
                    '#' if 4 <= no => v[i][j] = 'L',
                    _ => (),
                }
            }
        }
        World::from(v)
    }
    fn next2(&mut self) -> Self {
        let mut v: Vec<Vec<char>> = self.data.clone();
        for i in 0..self.data.len() {
            for j in 0..self.data[0].len() {
                let no = self.num_occupied_around_through(i, j);
                match self.at(i, j) {
                    'L' if no == 0 => v[i][j] = '#',
                    '#' if 5 <= no => v[i][j] = 'L',
                    _ => (),
                }
            }
        }
        World::from(v)
    }

    fn print(&self) {
        for v in &self.data {
            for c in v {
                print!("{}", c);
            }
            println!();
        }
    }
}

pub fn day11() {
    let mut buffer = String::new();
    io::stdin().read_to_string(&mut buffer).expect("wrong");

    let mut place: Vec<Vec<char>> = Vec::new();
    for l in buffer.split('\n') {
        if l.is_empty() {
            break;
        }
        let mut vec: Vec<char> = Vec::new();
        for c in l.chars() {
            vec.push(c);
        }
        place.push(vec);
    }
    let mut world: World = World::from(place);
    let mut n = 0;
    loop {
        n += 1;
        // let next = world.next();
        let next = world.next2();
        if world == next {
            panic!("stabilized at {} with {}", n, next.num_occupied());
        }
        world = next;
    }
}
