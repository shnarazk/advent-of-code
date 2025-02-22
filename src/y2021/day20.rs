//! <https://adventofcode.com/2021/day/20>
use crate::{
    framework::{AdventOfCode, ParseError, aoc},
    geometric,
};

#[derive(Clone, Debug, Default)]
pub struct Puzzle {
    enhancer: Vec<char>,
    image: Vec<Vec<char>>,
}

#[aoc(2021, 20)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, input: &str) -> Result<(), ParseError> {
        for block in input.split("\n\n").filter(|b| !b.is_empty()) {
            let first_block = self.enhancer.is_empty();
            for l in block.split('\n') {
                if l.is_empty() {
                    continue;
                }
                if first_block {
                    self.enhancer.append(&mut l.chars().collect::<Vec<char>>());
                } else {
                    self.image.push(l.chars().collect::<Vec<char>>());
                }
            }
        }
        debug_assert_eq!(self.enhancer.len(), 512);
        Self::parsed()
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut image = self.image.clone();
        for count in 0..2 {
            let c = if count % 2 == 0 { '.' } else { '#' };
            for v in image.iter_mut() {
                v.insert(0, c);
                v.insert(0, c);
                v.insert(0, c);
                v.push(c);
                v.push(c);
                v.push(c);
            }
            let mut v = Vec::new();
            v.resize(image[0].len(), c);
            image.insert(0, v.clone());
            image.insert(0, v.clone());
            image.insert(0, v.clone());
            image.push(v.clone());
            image.push(v.clone());
            image.push(v.clone());

            // println!("before {}", count);
            // for v in image.iter() {
            //     println!("{}", v.iter().collect::<String>());
            // }

            let height = image.len();
            let width = image[0].len();
            let mut next = image.clone();

            for (j, v) in next.iter_mut().enumerate() {
                for (i, n) in v.iter_mut().enumerate() {
                    let key: usize = geometric::neighbors9(j, i, height, width)
                        .iter()
                        .map(|(jj, ii)| (image[*jj][*ii] == '#') as usize)
                        .fold(0, |t, x| 2 * t + x);
                    *n = self.enhancer[key];
                }
            }

            if count == 1 {
                // trim outer frame
                for v in next.iter_mut() {
                    v.remove(0);
                    v.pop().unwrap();
                }
                next.remove(0);
                next.pop();
            }

            std::mem::swap(&mut image, &mut next);
            // println!("after {}", count);
            // for v in image.iter() {
            //     println!("{}", v.iter().collect::<String>());
            // }
        }
        // println!();
        // for v in image.iter() {
        //     println!("{}", v.iter().collect::<String>());
        // }
        image
            .iter()
            .map(|v| v.iter().filter(|c| **c == '#').count())
            .sum()
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut image = self.image.clone();
        for count in 0..50 {
            let c = if count % 2 == 0 { '.' } else { '#' };
            for v in image.iter_mut() {
                v.insert(0, c);
                v.insert(0, c);
                v.insert(0, c);
                v.push(c);
                v.push(c);
                v.push(c);
            }
            let mut v = Vec::new();
            v.resize(image[0].len(), c);
            image.insert(0, v.clone());
            image.insert(0, v.clone());
            image.insert(0, v.clone());
            image.push(v.clone());
            image.push(v.clone());
            image.push(v.clone());

            let height = image.len();
            let width = image[0].len();
            let mut next = image.clone();

            for (j, v) in next.iter_mut().enumerate() {
                for (i, n) in v.iter_mut().enumerate() {
                    let key: usize = geometric::neighbors9(j, i, height, width)
                        .iter()
                        .map(|(jj, ii)| (image[*jj][*ii] == '#') as usize)
                        .fold(0, |t, x| 2 * t + x);
                    *n = self.enhancer[key];
                }
            }

            if count != 100 {
                // trim outer frame
                for v in next.iter_mut() {
                    v.remove(0);
                    v.pop().unwrap();
                }
                next.remove(0);
                next.pop();
            }

            std::mem::swap(&mut image, &mut next);
            /*
            println!("after {}", count);
            for v in image.iter() {
                println!("{}", v.iter().collect::<String>());
            }
            */
        }
        // println!();
        // for v in image.iter() {
        //     println!("{}", v.iter().collect::<String>());
        // }
        image
            .iter()
            .map(|v| v.iter().filter(|c| **c == '#').count())
            .sum()
    }
}
