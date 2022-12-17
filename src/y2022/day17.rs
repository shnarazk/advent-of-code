//! <https://adventofcode.com/2022/day/17>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::neighbors,
        line_parser, regex,
    },
    std::collections::{HashMap, HashSet},
};

type Loc = (usize, usize);

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<isize>,
}

#[aoc(2022, 17)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        dbg!(block);
        if !block.is_empty() {
            self.line = block
                .trim()
                .chars()
                .map(|c| (c == '>') as usize as isize * 2 - 1)
                .collect::<Vec<isize>>();
        }
        Ok(())
    }
    fn after_insert(&mut self) {
        dbg!(&self.line.len());
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut window = self.line.iter().cycle();
        macro_rules! blow {
            ($x: expr, $w: expr) => {
                // ($x as isize + window.next().unwrap()).clamp(1, 8 - $w) as usize
                {
                    let w = *window.next().unwrap();
                    // println!("{}", if 0 < w { "right" } else { "left" });
                    ($x as isize + w).clamp(1, 8 - $w) as usize
                }
            };
        }
        let mut blocks: HashSet<Loc> = HashSet::new();
        for i in 0..7 {
            blocks.insert((i, 0));
        }
        let shape = [
            vec![(0, 0), (1, 0), (2, 0), (3, 0)],
            vec![(1, 0), (0, 1), (1, 1), (2, 1), (1, 2)],
            vec![(0, 0), (1, 0), (2, 0), (2, 1), (2, 2)],
            vec![(0, 0), (0, 1), (0, 2), (0, 3)],
            vec![(0, 0), (1, 0), (0, 1), (1, 1)],
        ];
        let shape_w = [4, 3, 3, 1, 2];
        let shape_h = [1, 3, 3, 4, 2];
        let mut bottom = 0;
        for i in 0..2022 {
            let id = i % 5;
            let mut x: usize = 3;
            let mut y = bottom + 4;
            loop {
                let tmp_x = blow!(x, shape_w[id]);
                if !clash((tmp_x, y), &shape[id], &blocks) {
                    x = tmp_x;
                }
                let tmp_y = y - 1;
                if clash((x, tmp_y), &shape[id], &blocks) {
                    break;
                }
                y = tmp_y;
            }
            bottom = place((x, y), &shape[id], &mut blocks);
            // print(&blocks);
            // assert!(i < 3);
        }
        bottom
    }
    fn part2(&mut self) -> Self::Output2 {
        0
    }
}

fn clash(loc: Loc, shape: &[Loc], map: &HashSet<Loc>) -> bool {
    shape
        .iter()
        .any(|(x, y)| map.contains(&(x + loc.0, y + loc.1)))
}

fn place(loc: Loc, shape: &[Loc], map: &mut HashSet<Loc>) -> usize {
    for (x, y) in shape.iter() {
        map.insert((x + loc.0, y + loc.1));
    }
    map.iter().map(|(_, y)| *y).max().unwrap_or_default()
}

fn print(map: &HashSet<Loc>) {
    for y in (1..(2 + map.iter().map(|(_, y)| *y).max().unwrap_or_default())).rev() {
        print!("|");
        for x in 1..=7 {
            print!("{}", if map.contains(&(x, y)) { '#' } else { '.' });
        }
        println!("|");
    }
    println!("+-------+");
}
