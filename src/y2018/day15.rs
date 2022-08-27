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
const DIRS: [Dim2; 4] = [(-1, 0), (0, 1), (1, 0), (0, -1)];

fn mdist(a: &Dim2, b: &Dim2) -> usize {
    a.0.abs_diff(b.0) + a.1.abs_diff(b.1)
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
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
    fn is_elf(&self) -> bool {
        matches!(self, Creature::Elf(_, _))
    }
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
    // Eeometry
    //
    //
    // Moving
    //
    fn target_creatures<'a, 'b>(&'a self, world: &'b Puzzle) -> Vec<&'b Creature> {
        world
            .creatures
            .iter()
            .filter(|c| self.is_elf() != c.is_elf())
            .collect::<Vec<_>>()
    }
    fn all_ranges(&self, world: &Puzzle) -> Vec<Dim2> {
        let v = self.target_creatures(world);
        let mut valids: HashSet<Dim2> = HashSet::new();
        for c in v.iter() {
            let p = c.position();
            for adj in DIRS {
                let q = (p.0 + adj.0, p.1 + adj.1);
                if world.map.contains(&q) {
                    valids.insert(q);
                }
            }
        }
        let pos = self.position();
        let mut p: Vec<Dim2> = valids.iter().copied().collect::<Vec<_>>();
        p.sort_by_key(|t| mdist(t, pos));
        p
    }
    fn best_moving_position(&self, world: &Puzzle) -> Option<Dim2> {
        let mut v = self.all_ranges(world);
        (!v.is_empty()).then(|| {
            v.sort();
            v[0]
        })
    }
    fn is_in_a_range<'a, 'b>(&'a self, world: &'b Puzzle) -> Option<Vec<&'b Creature>> {
        let p = self.position();
        let enemies = self.target_creatures(world);
        let mut targets: HashSet<&Creature> = HashSet::new();
        for adj in DIRS {
            let q = (p.0 + adj.0, p.1 + adj.1);
            for e in enemies.iter() {
                if e.position() == p {
                    targets.insert(*e);
                }
            }
        }
        (!targets.is_empty()).then(|| {
            let mut v = targets.iter().copied().collect::<Vec<_>>();
            v.sort();
            v
        })
    }
    //
    // Attacking
    //
    fn best_target_creature(&self, world: &Puzzle) -> Option<Creature> {
        let mut v = self.target_creatures(world);
        (!v.is_empty()).then(|| {
            v.sort();
            v[0].clone()
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
        if let Some(v) = self.is_in_a_range(world) {
            todo!();
        } else {
            dbg!(self.best_moving_position(world));
            todo!();
        }
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
        self.creatures.sort();
        let mut c = self.creatures[0].clone();
        dbg!(&c);
        c.turn(self);
        0
    }
    fn part2(&mut self) -> Self::Output2 {
        0
    }
}
