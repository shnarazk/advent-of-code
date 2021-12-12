use crate::{
    framework::{aoc, AdventOfCode, Maybe},
    line_parser,
};

fn rotating_go_forward(
    acum: &mut [usize; 7],
    index: usize,
    birth1: &mut usize,
    birth2: &mut usize,
) {
    let matured = *birth2;
    *birth2 = *birth1;
    *birth1 = acum[index];
    acum[index] += matured;
}

fn go_forward(vec: &mut Vec<usize>) {
    let mut news = 0;
    for i in vec.iter_mut() {
        if *i == 0 {
            news += 1;
            *i = 6;
        } else {
            *i -= 1;
        }
    }
    for _ in 0..news {
        vec.push(8);
    }
}

#[derive(Debug, Default)]
pub struct Puzzle {
    vec: Vec<usize>,
}

#[aoc(2021, 6)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Maybe<()> {
        self.vec = line_parser::to_usizes(block, ',')?;
        Ok(())
    }
    fn part1(&mut self) -> usize {
        let mut vec = self.vec.clone();
        for _ in 0..80 {
            go_forward(&mut vec);
        }
        vec.len()
    }
    fn part2(&mut self) -> usize {
        let mut acum = [0; 7];
        for i in self.vec.iter() {
            acum[*i] += 1;
        }
        let mut birth1 = 0;
        let mut birth2 = 0;
        for i in 0..256 {
            rotating_go_forward(&mut acum, i % 7, &mut birth1, &mut birth2);
            // dbg!(acum.iter().sum::<usize>() + pre1 + pre2);
        }
        acum.iter().sum::<usize>() + birth1 + birth2
    }
}
