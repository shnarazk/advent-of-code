//! <https://adventofcode.com/2018/day/22>
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric,
    },
    std::{
        cmp::Reverse,
        collections::{BinaryHeap, HashMap},
    },
};

type Dim2 = (usize, usize);

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Tool {
    Neither,
    ClimbingGear,
    Torch,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum RegionType {
    Rocky,
    Narrow,
    Wet,
}

const SUITABLE_TOOLS: [[Tool; 2]; 3] = [
    [Tool::ClimbingGear, Tool::Torch],
    [Tool::Neither, Tool::ClimbingGear],
    [Tool::Neither, Tool::Torch],
];

impl RegionType {
    fn risk(&self) -> usize {
        match self {
            RegionType::Rocky => 0,
            RegionType::Narrow => 2,
            RegionType::Wet => 1,
        }
    }
    fn suitable_tools(&self) -> &[Tool; 2] {
        match self {
            RegionType::Rocky => &SUITABLE_TOOLS[0],
            RegionType::Narrow => &SUITABLE_TOOLS[2],
            RegionType::Wet => &SUITABLE_TOOLS[1],
        }
    }
}

#[derive(Debug, Default, Eq, PartialEq)]
pub struct Puzzle {
    depth: usize,
    target: Dim2,
    geologic_index_map: HashMap<Dim2, usize>,
    erosion_level_map: HashMap<Dim2, usize>,
    region_type_map: HashMap<Dim2, RegionType>,
}

#[aoc(2018, 22)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, _: &str) -> Result<(), ParseError> {
        Ok(())
    }
    fn wrap_up(&mut self) {
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
        // self.depth = 510;
        // self.target = (10, 10);
        let margin = 100;
        let target = (self.target.0 + margin, self.target.1 + margin);
        let _ = self.total_risk_level(&target);
        let mut cost_map: HashMap<(Dim2, Tool), usize> = HashMap::new();
        let mut to_visit: BinaryHeap<Reverse<(usize, (Dim2, Tool))>> = BinaryHeap::new();
        to_visit.push(Reverse((0, ((0, 0), Tool::Torch))));
        while let Some(Reverse((cost, (pos, tool)))) = to_visit.pop() {
            if pos == self.target {
                if tool != Tool::Torch {
                    to_visit.push(Reverse((cost + 7, (pos, Tool::Torch))));
                    continue;
                }
                return cost;
            }
            if cost_map.contains_key(&(pos, tool)) {
                continue;
            }
            cost_map.insert((pos, tool), cost);
            let region_type = self.region_type_map.get(&pos).unwrap();
            for tl in region_type.suitable_tools().iter() {
                for next in geometric::neighbors4(
                    pos.0,
                    pos.1,
                    self.target.0 + margin,
                    self.target.1 + margin,
                )
                .iter()
                {
                    let next_region = self.region_type_map.get(next).unwrap();
                    if cost_map.contains_key(&(*next, *tl)) {
                        continue;
                    }
                    if next_region.suitable_tools().contains(tl) {
                        to_visit.push(Reverse((
                            cost + if *tl == tool { 1 } else { 8 },
                            (*next, *tl),
                        )));
                    }
                }
            }
        }
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
        if let Some(val) = self.region_type_map.get(pos) {
            return *val;
        }
        let val = match self.erosion_level(pos) % 3 {
            0 => RegionType::Rocky,
            1 => RegionType::Wet,
            2 => RegionType::Narrow,
            _ => unreachable!(),
        };
        self.region_type_map.insert(*pos, val);
        val
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
