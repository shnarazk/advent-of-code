use crate::{
    framework::{aoc_at, AdventOfCode, Maybe},
    line_parser,
};

fn progress(
    vec: &mut [Vec<usize>],
    flash: Vec<(usize, usize)>,
    mut step: usize,
    mut total: usize,
) -> usize {
    let h = vec.len();
    let w = vec[0].len();
    let mut secondary: Vec<(usize, usize)> = Vec::new();
    if flash.is_empty() {
        assert!(vec.iter().all(|v| v.iter().all(|i| *i <= 9)));
        if step == 0 {
            for v in vec.iter() {
                for i in v.iter() {
                    print!("{}", i);
                }
                println!();
            }
            println!();
            return total;
        }
        for (j, v) in vec.iter_mut().enumerate() {
            for (i, p) in v.iter_mut().enumerate() {
                if *p == 9 {
                    secondary.push((j, i));
                }
                *p += 1;
            }
        }
    }
    for (j, i) in flash.iter() {
        for jj in [Some(*j), j.checked_sub(1), (j + 1 < h).then(|| j + 1)] {
            for ii in [Some(*i), i.checked_sub(1), (i + 1 < w).then(|| i + 1)] {
                if let (Some(y), Some(x)) = (jj, ii) {
                    if *j != y || *i != x {
                        if vec[y][x] == 9 {
                            secondary.push((y, x))
                        }
                        vec[y][x] += 1;
                    }
                }
            }
        }
    }
    total += flash.len();
    if secondary.is_empty() {
        for v in vec.iter_mut() {
            for i in v.iter_mut() {
                if 9 < *i {
                    *i = 0;
                }
            }
        }
        step -= 1;
    }
    // dbg!(step, flash.is_empty());
    progress(vec, secondary, step, total)
}

fn progress_check(vec: &mut [Vec<usize>], flash: Vec<(usize, usize)>, mut step: usize) -> usize {
    let h = vec.len();
    let w = vec[0].len();
    let mut secondary: Vec<(usize, usize)> = Vec::new();
    if flash.is_empty() {
        if vec.iter().all(|v| v.iter().all(|i| *i == 0)) {
            return step;
        }
        for (j, v) in vec.iter_mut().enumerate() {
            for (i, p) in v.iter_mut().enumerate() {
                if *p == 9 {
                    secondary.push((j, i));
                }
                *p += 1;
            }
        }
    }
    for (j, i) in flash.iter() {
        for jj in [Some(*j), j.checked_sub(1), (j + 1 < h).then(|| j + 1)] {
            for ii in [Some(*i), i.checked_sub(1), (i + 1 < w).then(|| i + 1)] {
                if let (Some(y), Some(x)) = (jj, ii) {
                    if *j != y || *i != x {
                        if vec[y][x] == 9 {
                            secondary.push((y, x))
                        }
                        vec[y][x] += 1;
                    }
                }
            }
        }
    }
    if secondary.is_empty() {
        for v in vec.iter_mut() {
            for i in v.iter_mut() {
                if 9 < *i {
                    *i = 0;
                }
            }
        }
        step += 1;
    }
    progress_check(vec, secondary, step)
}

#[derive(Debug, PartialEq)]
pub struct Puzzle {
    line: Vec<Vec<usize>>,
}

#[aoc_at(2021, 11)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn default() -> Self {
        Self { line: Vec::new() }
    }
    fn insert(&mut self, block: &str) -> Maybe<()> {
        self.line.push(line_parser::to_digits(block)?);
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        progress(&mut self.line, Vec::new(), 100, 0)
    }
    fn part2(&mut self) -> Self::Output2 {
        progress_check(&mut self.line, Vec::new(), 0)
    }
}
