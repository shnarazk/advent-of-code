//! <https://adventofcode.com/2018/day/24>
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

#[derive(Debug, Default, Eq, Hash, PartialEq)]
enum AttackType {
    Bludgeoning,
    Cold,
    Fire,
    Radiation,
    #[default]
    Slashing,
}

impl TryFrom<&str> for AttackType {
    type Error = ();
    fn try_from(value: &str) -> Result<Self, Self::Error> {
        match value {
            "cold" => Ok(AttackType::Cold),
            "bludgeoning" => Ok(AttackType::Bludgeoning),
            "fire" => Ok(AttackType::Fire),
            "radiation" => Ok(AttackType::Radiation),
            "slashing" => Ok(AttackType::Slashing),
            _ => Err(()),
        }
    }
}

#[derive(Debug, Default, Eq, PartialEq)]
struct Group {
    id: usize,
    units: usize,
    hitpoints: usize,
    weak_to: HashSet<AttackType>,
    immune_to: HashSet<AttackType>,
    attack: AttackType,
    damage: usize,
    initiative: usize,
}

#[derive(Debug, Default, Eq, PartialEq)]
pub struct Puzzle {
    immune: Vec<Group>,
    infection: Vec<Group>,
    reading_type_is_immune: bool,
}

#[aoc(2018, 24)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        // 801 units each with 4706 hit points (weak to radiation) with an attack that does 116 bludgeoning damage at initiative 1
        // 4485 units each with 2961 hit points (immune to radiation; weak to fire, cold) with an attack that does 12 slashing damage at initiative 4
        let set_type = regex!("(Immune System|Infection):");
        if let Some(set_type) = set_type.captures(block) {
            self.reading_type_is_immune = &set_type[0] == "Immune System";
            return Ok(());
        }
        // dbg!(&block);
        let parser = regex!(
            r"^(\d+) units each with (\d+) hit points( \([^)]+\))? with an attack that does (\d+) (\w+) damage at initiative (\d+)$"
        );
        let segment = parser.captures(block).ok_or(ParseError)?;
        // dbg!(&segment);
        let mut weak_to: HashSet<AttackType> = HashSet::new();
        let mut immune_to: HashSet<AttackType> = HashSet::new();
        if let Some(attrs) = segment.get(3) {
            for attr in attrs.as_str().split(';') {
                let target = attr.trim().trim_matches('(').trim_matches(')');
                let parser2 = regex!(r"(weak|immune) to (.*)$");
                let attributes = parser2.captures(target).ok_or(ParseError)?;
                if &attributes[1] == "weak" {
                    for word in attributes[2].split(", ") {
                        weak_to.insert(AttackType::try_from(word).unwrap());
                    }
                } else {
                    for word in attributes[2].split(", ") {
                        immune_to.insert(AttackType::try_from(word).unwrap());
                    }
                }
            }
        }
        if self.reading_type_is_immune {
            self.immune.push(Group {
                id: self.immune.len(),
                units: segment[1].parse::<usize>()?,
                hitpoints: segment[2].parse::<usize>()?,
                weak_to,
                immune_to,
                attack: AttackType::try_from(&segment[5]).map_err(|_| ParseError)?,
                damage: segment[4].parse::<usize>()?,
                initiative: segment[6].parse::<usize>()?,
            });
        } else {
            self.infection.push(Group {
                id: self.infection.len(),
                units: segment[1].parse::<usize>()?,
                hitpoints: segment[2].parse::<usize>()?,
                weak_to,
                immune_to,
                attack: AttackType::try_from(&segment[5]).map_err(|_| ParseError)?,
                damage: segment[4].parse::<usize>()?,
                initiative: segment[6].parse::<usize>()?,
            });
        }
        Ok(())
    }
    fn after_insert(&mut self) {
        dbg!(&self.immune);
        dbg!(&self.infection);
    }
    fn part1(&mut self) -> Self::Output1 {
        0
    }
    fn part2(&mut self) -> Self::Output2 {
        0
    }
}
