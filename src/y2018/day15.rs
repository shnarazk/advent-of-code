//! <https://adventofcode.com/2018/day/15>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::neighbors,
    },
    std::collections::HashSet,
};

type Dim2 = (isize, isize);

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
enum Creature {
    Elf(Dim2, usize),
    Goblin(Dim2, usize),
}

impl PartialOrd for Creature {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.position().partial_cmp(other.position())
    }
}

impl Ord for Creature {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.position().cmp(other.position())
    }
}

impl Creature {
    fn hit_point(&self) -> &usize {
        match self {
            Creature::Elf(_, hp) => hp,
            Creature::Goblin(_, hp) => hp,
        }
    }
    fn position(&self) -> &Dim2 {
        match self {
            Creature::Elf(p, _) => p,
            Creature::Goblin(p, _) => p,
        }
    }
    //
    // Moving
    //
    fn target_creatures(&self, world: &Puzzle) -> Vec<Creature> {
        todo!()
    }
    fn all_ranges(&self, world: &Puzzle) -> Vec<Dim2> {
        let v = self.target_creatures(world);
        todo!()
    }
    fn best_moving_position(&self, world: &Puzzle) -> Option<Dim2> {
        let v = self.all_ranges(world);
        todo!()
    }
    fn is_in_a_range(&self, world: &Puzzle) -> bool {
        todo!()
    }
    //
    // Attacking
    //
    fn best_target_creature(&self, world: &Puzzle) -> Option<Creature> {
        let mut v = self.target_creatures(world);
        (!v.is_empty()).then(|| {
            v.sort();
            v[0]
        })
    }
    /// return true if I'm killed.
    fn attacked(&mut self, world: &mut Puzzle) -> bool {
        let p = match self {
            Creature::Elf(_, hp) => hp,
            Creature::Goblin(_, hp) => hp,
        };
        if *p < 3 {
            world.creatures.retain(|c| c != self);
            return true;
        }
        *p -= 3;
        false
    }
    fn turn(&mut self, world: &mut Puzzle) -> bool {
        todo!()
    }
}

#[derive(Debug, Default, Eq, PartialEq)]
pub struct Puzzle {
    line: Vec<Vec<u8>>,
    map: HashSet<Dim2>,
    creatures: Vec<Creature>,
}

#[aoc(2018, 15)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.line
            .push(block.chars().map(|c| c as u8).collect::<Vec<u8>>());
        Ok(())
    }
    fn after_insert(&mut self) {
        for (j, l) in self.line.iter().enumerate() {
            for (i, c) in l.iter().enumerate() {
                let pos = (j as isize, i as isize);
                if *c != b'#' {
                    self.map.insert(pos);
                }
                match *c {
                    b'G' => {
                        self.creatures.push(Creature::Elf(pos, 300));
                    }
                    b'E' => {
                        self.creatures.push(Creature::Goblin(pos, 300));
                    }
                    _ => (),
                }
            }
        }
        dbg!(self.creatures.len());
    }
    fn part1(&mut self) -> Self::Output1 {
        0
    }
    fn part2(&mut self) -> Self::Output2 {
        0
    }
}
