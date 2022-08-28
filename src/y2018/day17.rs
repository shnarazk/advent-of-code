//! <https://adventofcode.com/2018/day/17>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::neighbors,
        line_parser, regex,
    },
    std::collections::HashSet,
};

type Dim2 = (usize, usize);

#[derive(Debug, Default, Eq, PartialEq)]
pub struct Puzzle {
    line: Vec<(bool, usize, usize, usize)>,
    map: HashSet<Dim2>,
    depth: usize,
    width: usize,
}

#[aoc(2018, 17)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        // x=550, y=1443..1454
        let parser = regex!(r"^(x|y)=(\d+), (x|y)=(\d+)\.\.(\d+)$");
        let segment = parser.captures(block).ok_or(ParseError)?;
        assert!(
            (&segment[1] == "x" && &segment[3] == "y")
                || (&segment[1] == "y" && &segment[3] == "x")
        );
        // println!(
        //     "{}={}; {}..{}",
        //     &segment[1], &segment[2], &segment[4], &segment[5]
        // );
        self.line.push((
            &segment[1] != "x",
            segment[2].parse::<usize>()?,
            segment[4].parse::<usize>()?,
            segment[5].parse::<usize>()?,
        ));
        Ok(())
    }
    fn after_insert(&mut self) {
        dbg!(&self.line.len());
        for (horizontal, base, from, to) in self.line.iter() {
            for i in *from..=*to {
                let p = if *horizontal { (*base, i) } else { (i, *base) };
                self.map.insert(p);
            }
        }
        dbg!(self.map.len());
        self.width = self.map.iter().map(|(y, x)| *x).max().unwrap();
        self.depth = self.map.iter().map(|(y, x)| *y).max().unwrap();
    }
    fn part1(&mut self) -> Self::Output1 {
        dbg!(basin_below((0, 500), self));
        0
    }
    fn part2(&mut self) -> Self::Output2 {
        0
    }
}

fn basin_below(start: Dim2, world: &Puzzle) -> Option<(usize, Option<Dim2>, Option<Dim2>)> {
    for y in start.0..world.depth {
        if world.map.contains(&(y, start.1)) {
            let bottom = (y, start.1);
            dbg!(bottom);
            let west = west_end(bottom, world);
            let east = east_end(bottom, world);
            // This is a bad idea.
            // There is a situation with a 'straw' that doesn't touch with the external basin.
            match west.0.cmp(&east.0) {
                std::cmp::Ordering::Less => {
                    println!("west: {:?} > east: {:?}", west, east);
                }
                std::cmp::Ordering::Equal => {
                    println!("west: {:?} = east: {:?}", west, east);
                }
                std::cmp::Ordering::Greater => {
                    println!("west: {:?} < east: {:?}", west, east);
                }
            }
            break;
        }
    }
    None
}

fn east_end(start: Dim2, world: &Puzzle) -> Dim2 {
    let mut point = start;
    loop {
        let mut check = (point.0, point.1 + 1);
        if world.map.contains(&check) {
            point = check;
            continue;
        }
        check = (point.0 - 1, point.1);
        if world.map.contains(&check) {
            point = check;
            continue;
        }
        break;
    }
    point
}

fn west_end(start: Dim2, world: &Puzzle) -> Dim2 {
    let mut point = start;
    loop {
        let mut check = (point.0, point.1 - 1);
        if world.map.contains(&check) {
            point = check;
            continue;
        }
        check = (point.0 - 1, point.1);
        if world.map.contains(&check) {
            point = check;
            continue;
        }
        break;
    }
    point
}
