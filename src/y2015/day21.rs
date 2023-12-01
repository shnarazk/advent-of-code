//! <https://adventofcode.com/2015/day/21>
use crate::framework::{aoc, AdventOfCode, ParseError};

const WEAPONS: [(&str, usize, usize, usize); 5] = [
    //Weapons:    Cost  Damage  Armor
    ("Dagger", 8, 4, 0),
    ("Shortsword", 10, 5, 0),
    ("Warhammer", 25, 6, 0),
    ("Longsword", 40, 7, 0),
    ("Greataxe", 74, 8, 0),
];

const ARMOR: [(&str, usize, usize, usize); 1 + 5] = [
    //Armor:      Cost  Damage  Armor
    ("No Armor", 0, 0, 0),
    ("Leather", 13, 0, 1),
    ("Chainmail", 31, 0, 2),
    ("Splintmail", 53, 0, 3),
    ("Bandedmail", 75, 0, 4),
    ("Platemail", 102, 0, 5),
];

const RINGS: [(&str, usize, usize, usize, [usize; 2]); 1 + 6 + 15] = [
    // Rings:      Cost  Damage  Armor
    ("No Rings", 25, 0, 0, [0, 0]),   // 0
    ("Damage +1", 25, 1, 0, [1, 0]),  // 1
    ("Damage +2", 50, 2, 0, [2, 0]),  // 2
    ("Damage +3", 100, 3, 0, [3, 0]), // 3
    ("Defense +1", 20, 0, 1, [4, 0]), // 4
    ("Defense +2", 40, 0, 2, [5, 0]), // 5
    ("Defense +3", 80, 0, 3, [6, 0]), // 6
    ("Da+1Da+2", 75, 3, 0, [1, 2]),   // 7
    ("Da+1Da+3", 125, 5, 0, [1, 3]),  // 8
    ("Da+1De+1", 45, 1, 1, [1, 4]),   // 9
    ("Da+1De+2", 65, 1, 2, [1, 5]),   // 10
    ("Da+1De+3", 105, 1, 3, [1, 6]),  // 11
    ("Da+2Da+3", 150, 5, 0, [2, 3]),  // 12
    ("Da+2De+1", 70, 2, 1, [2, 4]),   // 13
    ("Da+2De+2", 90, 2, 2, [2, 5]),   // 14
    ("Da+2De+3", 130, 2, 3, [2, 6]),  // 15
    ("Da+3De+1", 120, 3, 1, [3, 4]),  // 16
    ("Da+3De+2", 140, 3, 2, [3, 5]),  // 17
    ("Da+3De+3", 180, 3, 3, [3, 6]),  // 18
    ("De+1De+2", 60, 0, 3, [4, 5]),   // 19
    ("De+1De+3", 100, 0, 4, [4, 6]),  // 20
    ("De+2De+3", 120, 0, 5, [5, 6]),  // 21
];

#[derive(Clone, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
struct Inventory {
    weapon: usize,
    armor: usize,
    ring: usize,
    cost: usize,
}

#[allow(dead_code)]
impl Inventory {
    fn set_cost(&mut self) {
        self.cost = WEAPONS[self.weapon].1 + ARMOR[self.armor].1 + RINGS[self.ring].1;
    }
    fn compatible(&self, other: &Inventory) -> bool {
        (self.weapon != other.weapon)
            && (self.armor == 0 || other.armor == 0 || self.armor != other.armor)
            && RINGS[self.ring]
                .4
                .iter()
                .all(|r| *r == 0 || !RINGS[other.ring].4.contains(r))
    }
}

#[derive(Clone, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
struct State {
    hitpoint: usize,
    damage: usize,
    armor: usize,
}

impl State {
    fn beats(&mut self, enemy: &mut State) -> bool {
        assert!(0 < enemy.hitpoint);
        let hitpoint = if self.damage <= enemy.armor {
            if enemy.hitpoint == 1 {
                return true;
            }
            enemy.hitpoint - 1
        } else if enemy.hitpoint + enemy.armor <= self.damage {
            return true;
        } else {
            enemy.hitpoint + enemy.armor - self.damage
        };
        enemy.hitpoint = hitpoint;
        !enemy.beats(self)
    }
}

#[derive(Debug, Default, Eq, PartialEq)]
pub struct Puzzle {
    line: Vec<()>,
    invetories: Vec<Inventory>,
}

#[aoc(2015, 21)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, _block: &str) -> Result<(), ParseError> {
        Ok(())
    }
    fn end_of_data(&mut self) {
        for (weapon, w) in WEAPONS.iter().enumerate() {
            for (armor, a) in ARMOR.iter().enumerate() {
                for (ring, r) in RINGS.iter().enumerate() {
                    self.invetories.push(Inventory {
                        weapon,
                        armor,
                        ring,
                        cost: w.1 + a.1 + r.1,
                    });
                }
            }
        }
        self.invetories.sort_by_key(|i| i.cost);
        // dbg!(&self.invetories);
    }
    fn part1(&mut self) -> Self::Output1 {
        for i in self.invetories.iter() {
            let mut me = State {
                hitpoint: 100,
                damage: WEAPONS[i.weapon].2 + RINGS[i.ring].2,
                armor: ARMOR[i.armor].3 + RINGS[i.ring].3,
            };
            let mut boss = State {
                hitpoint: 103,
                damage: 9,
                armor: 2,
            };
            if me.beats(&mut boss) {
                return i.cost;
            }
        }
        0
    }
    fn part2(&mut self) -> Self::Output2 {
        self.invetories.reverse();
        for i in self.invetories.iter() {
            let mut me = State {
                hitpoint: 100,
                damage: WEAPONS[i.weapon].2 + RINGS[i.ring].2,
                armor: ARMOR[i.armor].3 + RINGS[i.ring].3,
            };
            let mut boss = State {
                hitpoint: 103,
                damage: 9,
                armor: 2,
            };
            if !me.beats(&mut boss) {
                return i.cost;
            }
        }
        0
    }
}
