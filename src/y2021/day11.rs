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
    } else {
        for (j, i) in flash.iter() {
            for dj in [-1isize, 0, 1] {
                if *j == 0 && dj == -1 {
                    continue;
                }
                if *j + 1 == h && dj == 1 {
                    continue;
                }
                for di in [-1, 0, 1] {
                    if *i == 0 && di == -1 {
                        continue;
                    }
                    if *i + 1 == w && di == 1 {
                        continue;
                    }
                    if dj == 0 && di == 0 {
                        continue;
                    }
                    let jj = (*j as isize + dj) as usize;
                    let ii = (*i as isize + di) as usize;
                    if vec[jj][ii] == 9 {
                        secondary.push((jj, ii))
                    }
                    vec[jj][ii] += 1;
                }
            }
        }
        total += flash.len();
    }
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
    } else {
        for (j, i) in flash.iter() {
            for dj in [-1isize, 0, 1] {
                if *j == 0 && dj == -1 {
                    continue;
                }
                if *j + 1 == h && dj == 1 {
                    continue;
                }
                for di in [-1, 0, 1] {
                    if *i == 0 && di == -1 {
                        continue;
                    }
                    if *i + 1 == w && di == 1 {
                        continue;
                    }
                    if dj == 0 && di == 0 {
                        continue;
                    }
                    let jj = (*j as isize + dj) as usize;
                    let ii = (*i as isize + di) as usize;
                    if vec[jj][ii] == 9 {
                        secondary.push((jj, ii))
                    }
                    vec[jj][ii] += 1;
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
