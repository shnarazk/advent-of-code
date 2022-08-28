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
    std::collections::{HashMap, HashSet},
};

type Dim2 = (usize, usize);

#[derive(Debug, Default, Eq, PartialEq)]
pub struct Puzzle {
    line: Vec<(bool, usize, usize, usize)>,
    map: HashSet<Dim2>,
    water_map: HashSet<Dim2>,
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
        // self.water_map.len()
        let start = (0, 500);
        let mut to_update: Vec<Dim2> = vec![start];
        let mut water: HashMap<Dim2, Water> = HashMap::new();
        while let Some(pos) = to_update.pop() {
            let state = water.get(&pos).unwrap();
            let above = water.get(&pos).unwrap();
            let left = water.get(&pos).unwrap();
            let right = water.get(&pos).unwrap();
            let below = water.get(&pos).unwrap();
            if let Some(next) = transition(state, above, left, right, below) {
                water.insert(pos, next);
                let left = (pos.0, pos.1 - 1);
                let right = (pos.0, pos.1 + 1);
                let below = (pos.0 + 1, pos.1);
                to_update.push(left);
                to_update.push(right);
                to_update.push(below);
            }
            self.render(&water);
        }
        water
            .values()
            .filter(|s| ![Water::None, Water::Block].contains(s))
            .count()
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
            // We must consider the situation in which water drops to the same basin 'recursively'.
            let possible_region = match west.0.cmp(&east.0) {
                std::cmp::Ordering::Less => {
                    println!("west: {:?} > east: {:?}", west, east);
                    ((east.0, west.1 + 1), (bottom.0, east.1))
                }
                std::cmp::Ordering::Equal => {
                    println!("west: {:?} = east: {:?}", west, east);
                    ((west.0, west.1 + 1), (bottom.0, east.1))
                }
                std::cmp::Ordering::Greater => {
                    println!("west: {:?} < east: {:?}", west, east);
                    ((west.0, west.1 + 1), (bottom.0, east.1))
                }
            };
            for y in (possible_region.0 .0 - 1)..possible_region.1 .0 {
                for x in (possible_region.0 .1 + 1)..possible_region.1 .1 {
                    if world.map.contains(&(y, x)) {
                        dbg!((y, x));
                        panic!();
                    }
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

#[derive(Debug, Eq, PartialEq, Ord, PartialOrd)]
enum Water {
    None,
    On,
    LeftBound,
    RightBound,
    BothBound,
    Block,
}

fn transition(
    state: &Water,
    above: &Water,
    left: &Water,
    right: &Water,
    below: &Water,
) -> Option<Water> {
    let dry = [Water::None, Water::Block];
    let solid = [Water::BothBound, Water::Block];
    let left_solid = [Water::LeftBound, Water::BothBound, Water::Block];
    let right_solid = [Water::RightBound, Water::BothBound, Water::Block];
    match (state, above, left, right, below) {
        (Water::Block, _, _, _, _) => None,
        (Water::None, a, _, _, _) if !dry.contains(a) => Some(Water::On),
        (Water::None, _, l, _, b) if !dry.contains(l) && solid.contains(b) => Some(Water::On),
        (Water::None, _, _, r, b) if !dry.contains(r) && solid.contains(b) => Some(Water::On),
        (Water::On, _, l, r, _) if left_solid.contains(l) && right_solid.contains(r) => {
            Some(Water::BothBound)
        }
        (Water::On, _, l, _, _) if left_solid.contains(l) => Some(Water::LeftBound),
        (Water::On, _, _, r, _) if right_solid.contains(r) => Some(Water::RightBound),

        (Water::LeftBound, _, _, r, _) if right_solid.contains(r) => Some(Water::BothBound),
        (Water::RightBound, _, l, _, _) if left_solid.contains(l) => Some(Water::BothBound),
        _ => None,
    }
}

impl Puzzle {
    fn render(&self, water: &HashMap<Dim2, Water>) {}
}
