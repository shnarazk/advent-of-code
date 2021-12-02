use crate::y2020::traits::{Description, ProblemObject, ProblemSolver};

pub fn day03(part: usize, desc: Description) {
    dbg!(Setting::parse(desc).run(part));
}

#[derive(Debug, PartialEq)]
struct Chars {
    char: Vec<char>,
}

impl ProblemObject for Chars {
    fn parse(s: &str) -> Option<Self> {
        if s.is_empty() {
            None
        } else {
            Some(Chars {
                char: s.chars().collect::<Vec<char>>(),
            })
        }
    }
}

#[derive(Debug, PartialEq)]
struct Setting {
    line: Vec<Chars>,
}

impl ProblemSolver<Chars, usize, usize> for Setting {
    const YEAR: usize = 2020;
    const DAY: usize = 3;
    const DELIMITER: &'static str = "\n";
    fn default() -> Self {
        Setting { line: Vec::new() }
    }
    fn insert(&mut self, object: Chars) {
        self.line.push(object);
    }
    fn part1(&mut self) -> usize {
        self.count_for_slope(1, 3)
    }
    fn part2(&mut self) -> usize {
        // println!("{}", self.count_for_slope(1, 1));
        // println!("{}", self.count_for_slope(1, 3));
        // println!("{}", self.count_for_slope(1, 5));
        // println!("{}", self.count_for_slope(1, 7));
        // println!("{}", self.count_for_slope(2, 1));
        self.count_for_slope(1, 1)
            * self.count_for_slope(1, 3)
            * self.count_for_slope(1, 5)
            * self.count_for_slope(1, 7)
            * self.count_for_slope(2, 1)
    }
}

impl Setting {
    fn count_for_slope(&self, row: usize, col: usize) -> usize {
        let mut r = row;
        let mut c = col;
        let mut occ = 0;
        while r < self.line.len() {
            occ += self.access(r, c);
            r += row;
            c += col;
        }
        occ
    }
    fn access(&self, row: usize, col: usize) -> usize {
        let line = &self.line[row].char;
        let c = col % line.len();
        (line[c] == '#') as usize
    }
}
