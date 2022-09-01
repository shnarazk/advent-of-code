//! <https://adventofcode.com/2018/day/22>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::neighbors,
    },
    std::collections::HashMap,
};

type Dim2 = (usize, usize);

#[derive(Debug, Eq, Hash, PartialEq)]
enum Tool {
    Neither,
    ClimbingGear,
    Torch,
}

#[derive(Debug, Eq, Hash, PartialEq)]
enum RegionType {
    Rocky,
    Narrow,
    Wet,
}

impl RegionType {
    fn risk(&self) -> usize {
        match self {
            RegionType::Rocky => 0,
            RegionType::Narrow => 2,
            RegionType::Wet => 1,
        }
    }
    fn suitable(&self, tool: &Tool) -> bool {
        matches!(
            (self, tool),
            (&RegionType::Rocky, &Tool::ClimbingGear)
                | (&RegionType::Rocky, &Tool::Torch)
                | (&RegionType::Wet, &Tool::Neither)
                | (&RegionType::Wet, &Tool::ClimbingGear)
                | (&RegionType::Narrow, &Tool::Neither)
                | (&RegionType::Narrow, &Tool::Torch)
        )
    }
}

#[derive(Debug, Default, Eq, PartialEq)]
pub struct Puzzle {
    depth: usize,
    target: Dim2,
    geologic_index_map: HashMap<Dim2, usize>,
    erosion_level_map: HashMap<Dim2, usize>,
}

#[aoc(2018, 22)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        Ok(())
    }
    fn after_insert(&mut self) {
        self.depth = 3066;
        self.target = (726, 13);
        // self.depth = 510;
        // self.target = (10, 10);
        // assert_eq!(self.erosion_level(&(0, 0)), 510);
        // assert_eq!(self.erosion_level(&(0, 1)), 17317);
        // assert_eq!(self.erosion_level(&(1, 1)), 1805);
        // assert_eq!(self.erosion_level(&(10, 10)), 510);
    }
    fn part1(&mut self) -> Self::Output1 {
        let target = self.target;
        self.total_risk_level(&target)
    }
    fn part2(&mut self) -> Self::Output2 {
        0
    }
}
impl Puzzle {
    fn geologic_index(&mut self, pos: &Dim2) -> usize {
        if let Some(val) = self.geologic_index_map.get(pos) {
            return *val;
        }
        let val = match pos {
            (0, 0) => 0,
            _ if *pos == self.target => 0,
            (0, x) => x * 16807,
            (y, 0) => y * 48271,
            (y, x) => self.erosion_level(&(*y, *x - 1)) * self.erosion_level(&(*y - 1, *x)),
        };
        self.geologic_index_map.insert(*pos, val);
        val
    }
    fn erosion_level(&mut self, pos: &Dim2) -> usize {
        if let Some(val) = self.erosion_level_map.get(pos) {
            return *val;
        }
        let val = (self.geologic_index(pos) + self.depth) % 20183;
        self.erosion_level_map.insert(*pos, val);
        val
    }
    fn region_type(&mut self, pos: &Dim2) -> RegionType {
        match self.erosion_level(pos) % 3 {
            0 => RegionType::Rocky,
            1 => RegionType::Wet,
            2 => RegionType::Narrow,
            _ => unreachable!(),
        }
    }
    fn total_risk_level(&mut self, pos: &Dim2) -> usize {
        let mut sum: usize = 0;
        for y in 0..=pos.0 {
            for x in 0..=pos.1 {
                sum += self.region_type(&(y, x)).risk();
            }
        }
        sum
    }
}
