use crate::{
    framework::{aoc_at, AdventOfCode, Maybe},
    line_parser,
};

#[derive(Debug, Default, PartialEq)]
pub struct Puzzle {
    line: Vec<Vec<usize>>,
    height: usize,
    width: usize,
    step: usize,
}

fn neighbors(here: usize, to: usize) -> [Option<usize>; 3] {
    [
        Some(here),
        here.checked_sub(1),
        (here + 1 < to).then(|| here + 1),
    ]
}

impl Puzzle {
    fn progress(&mut self, flash: Vec<(usize, usize)>, mut total: usize) -> usize {
        let mut secondary: Vec<(usize, usize)> = Vec::new();
        if flash.is_empty() {
            assert!(self.line.iter().all(|v| v.iter().all(|i| *i <= 9)));
            if self.step == 0 {
                for v in self.line.iter() {
                    for i in v.iter() {
                        print!("{}", i);
                    }
                    println!();
                }
                println!();
                return total;
            }
            for (j, v) in self.line.iter_mut().enumerate() {
                for (i, p) in v.iter_mut().enumerate() {
                    if *p == 9 {
                        secondary.push((j, i));
                    }
                    *p += 1;
                }
            }
        }
        for (j, i) in flash.iter() {
            for jj in neighbors(*j, self.height) {
                for ii in neighbors(*i, self.width) {
                    if let (Some(y), Some(x)) = (jj, ii) {
                        if *j != y || *i != x {
                            if self.line[y][x] == 9 {
                                secondary.push((y, x))
                            }
                            self.line[y][x] += 1;
                        }
                    }
                }
            }
        }
        total += flash.len();
        if secondary.is_empty() {
            for v in self.line.iter_mut() {
                for i in v.iter_mut() {
                    if 9 < *i {
                        *i = 0;
                    }
                }
            }
            self.step -= 1;
        }
        // dbg!(self.step, flash.is_empty());
        self.progress(secondary, total)
    }

    fn progress_check(&mut self, flash: Vec<(usize, usize)>) -> usize {
        let mut secondary: Vec<(usize, usize)> = Vec::new();
        if flash.is_empty() {
            if self.line.iter().all(|v| v.iter().all(|i| *i == 0)) {
                return self.step;
            }
            for (j, v) in self.line.iter_mut().enumerate() {
                for (i, p) in v.iter_mut().enumerate() {
                    if *p == 9 {
                        secondary.push((j, i));
                    }
                    *p += 1;
                }
            }
        }
        for (j, i) in flash.iter() {
            for jj in [
                Some(*j),
                j.checked_sub(1),
                (j + 1 < self.height).then(|| j + 1),
            ] {
                for ii in [
                    Some(*i),
                    i.checked_sub(1),
                    (i + 1 < self.width).then(|| i + 1),
                ] {
                    if let (Some(y), Some(x)) = (jj, ii) {
                        if *j != y || *i != x {
                            if self.line[y][x] == 9 {
                                secondary.push((y, x))
                            }
                            self.line[y][x] += 1;
                        }
                    }
                }
            }
        }
        if secondary.is_empty() {
            for v in self.line.iter_mut() {
                for i in v.iter_mut() {
                    if 9 < *i {
                        *i = 0;
                    }
                }
            }
            self.step += 1;
        }
        self.progress_check(secondary)
    }
}

#[aoc_at(2021, 11)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Maybe<()> {
        self.line.push(line_parser::to_digits(block)?);
        Ok(())
    }
    fn after_insert(&mut self) {
        self.height = self.line.len();
        self.width = self.line[0].len();
    }
    fn part1(&mut self) -> Self::Output1 {
        self.step = 100;
        self.progress(Vec::new(), 0)
    }
    fn part2(&mut self) -> Self::Output2 {
        self.progress_check(Vec::new())
    }
}
