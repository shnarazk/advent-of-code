//! <https://adventofcode.com/2015/day/22>
use crate::{
    framework::{aoc, AdventOfCode, ParseError},
    regex,
};

// (hitpoint, damage, armor, mana)
const SPELL: [(usize, usize, (usize, usize, usize, usize)); 5] = [
    (53, 1, (0, 4, 0, 0)),
    (73, 1, (2, 2, 0, 0)),
    (113, 6, (0, 0, 7, 0)),
    (173, 6, (0, 3, 0, 0)),
    (229, 5, (0, 0, 0, 101)),
];

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum GameState {
    #[default]
    Impossible,
    Won,
    Lose,
}

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Player {
    hit_point: usize,
    damage: usize,
    armor: usize,
    mana: usize,
    state: [Option<usize>; 5], // Magic Missile, Drain, Shild, Poison, Rechage
}

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Boss {
    hit_point: usize,
    damage: usize,
}

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    hit_point: usize,
    damage: usize,
    player: Player,
    boss: Boss,
}

impl Puzzle {
    // turn consists of your spell then boss's attack
    fn turn(&self, kind: usize) -> Result<Puzzle, GameState> {
        if self.player.state[kind].is_some() && self.player.mana < SPELL[kind].0 {
            return Err(GameState::Impossible);
        }
        let mut new_state = self.clone();
        // spelling
        new_state.player.state[kind] = Some(SPELL[kind].1);
        // your spell effects just before the boss's turn
        for (kind, _) in SPELL.iter().enumerate() {
            if let Some(remain) = &mut new_state.player.state[kind] {
                if 0 == *remain {
                    new_state.player.state[kind] = None;
                } else {
                    *remain -= 1;
                    new_state.player.hit_point += SPELL[kind].2 .0;
                    new_state.boss.hit_point -= SPELL[kind].2 .1;
                    new_state.player.armor += SPELL[kind].2 .2;
                    new_state.player.mana += SPELL[kind].2 .3;
                }
            }
        }
        // boss atack
        new_state.player.hit_point = new_state
            .player
            .hit_point
            .checked_sub(new_state.boss.damage)
            .ok_or(GameState::Lose)?;
        return Ok(new_state);
    }
}

// impl State {
//     fn spell(&self, kind: usize) -> Option<State> {
//         let mut s = self.clone();
//         s.born = true;
//         // your turn
//         match kind {
//             // Magic Missile
//             1 if 53 <= s.mana => {
//                 s.damage = 4;
//                 s.mana -= 53;
//                 s.used_mana += 53;
//             }
//             // Drain
//             2 if 73 <= s.mana => {
//                 s.damage = 2;
//                 s.hit_point += 2;
//                 s.mana -= 73;
//                 s.used_mana += 73;
//             }
//             // Shield
//             3 if 113 <= s.mana && s.extra_armor == 0 => {
//                 s.extra_armor = -6 - 1;
//                 s.mana -= 113;
//                 s.used_mana += 113;
//             }
//             3 if 113 <= s.mana && s.extra_armor == 1 => {
//                 s.extra_armor = 7;
//                 s.mana -= 113;
//                 s.used_mana += 113;
//             }
//             // Poison
//             4 if 173 <= s.mana && s.extra_damage == 0 => {
//                 s.extra_damage = -6 - 1;
//                 s.mana -= 173;
//                 s.used_mana += 173;
//             }
//             4 if 173 <= s.mana && s.extra_damage == 1 => {
//                 s.extra_damage = 7;
//                 s.mana -= 173;
//                 s.used_mana += 173;
//             }
//             // Shield
//             5 if 229 <= s.mana && s.extra_mana == 0 => {
//                 s.extra_mana = -5 - 1;
//                 s.mana -= 229;
//                 s.used_mana += 229;
//             }
//             5 if 229 <= s.mana && s.extra_mana == 1 => {
//                 s.extra_mana = 6;
//                 s.mana -= 229;
//                 s.used_mana += 229;
//             }
//             _ => {
//                 return None;
//             }
//         }
//         Some(s)
//     }
//     fn turn(&mut self, enemy: &mut State) {
//         assert!(0 < enemy.hit_point);
//         if 0 < self.extra_mana {
//             self.mana += 101;
//         }
//         let damage = if 0 < self.extra_damage {
//             self.damage + 3
//         } else {
//             self.damage
//         };
//         if enemy.hit_point <= damage {
//             enemy.hit_point = 0;
//             return;
//         } else {
//             enemy.hit_point -= damage;
//         }
//         self.damage = 0;
//         // enemy turn
//         self.extra_damage = self
//             .extra_damage
//             .abs()
//             .checked_sub(1)
//             .map_or_else(|| 0, |v| v);
//         self.extra_armor = self
//             .extra_armor
//             .abs()
//             .checked_sub(1)
//             .map_or_else(|| 0, |v| v);
//         self.extra_mana = self
//             .extra_mana
//             .abs()
//             .checked_sub(1)
//             .map_or_else(|| 0, |v| v);
//         if 0 < self.extra_mana {
//             self.mana += 101;
//         }
//         let armor = if 0 < self.extra_armor { 7 } else { 0 };

//         if 0 < self.extra_damage {
//             if enemy.hit_point <= 3 {
//                 enemy.hit_point = 0;
//                 return;
//             } else {
//                 enemy.hit_point -= 3;
//             }
//         }

//         if enemy.damage <= armor {
//             if self.hit_point == 1 {
//                 self.hit_point = 0;
//                 return;
//             }
//             self.hit_point -= 1;
//         } else if self.hit_point + armor <= enemy.damage {
//             self.hit_point = 0;
//             return;
//         } else {
//             self.hit_point -= enemy.damage - armor;
//         }
//         self.extra_damage = self
//             .extra_damage
//             .abs()
//             .checked_sub(1)
//             .map_or_else(|| 0, |v| v);
//         self.extra_armor = self
//             .extra_armor
//             .abs()
//             .checked_sub(1)
//             .map_or_else(|| 0, |v| v);
//         self.extra_mana = self
//             .extra_mana
//             .abs()
//             .checked_sub(1)
//             .map_or_else(|| 0, |v| v);
//     }
//     fn turn2(&mut self, enemy: &mut State) {
//         assert!(0 < enemy.hit_point);
//         if 0 < self.hit_point {
//             self.hit_point -= 1;
//         } else {
//             self.hit_point = 0;
//             return;
//         }
//         if 0 < self.extra_mana {
//             self.mana += 101;
//         }
//         let damage = if 0 < self.extra_damage {
//             self.damage + 3
//         } else {
//             self.damage
//         };
//         if enemy.hit_point <= damage {
//             enemy.hit_point = 0;
//             return;
//         } else {
//             enemy.hit_point -= damage;
//         }
//         self.damage = 0;
//         // enemy turn
//         if 0 < self.hit_point {
//             self.hit_point -= 1;
//         } else {
//             self.hit_point = 0;
//             return;
//         }
//         self.extra_damage = self
//             .extra_damage
//             .abs()
//             .checked_sub(1)
//             .map_or_else(|| 0, |v| v);
//         self.extra_armor = self
//             .extra_armor
//             .abs()
//             .checked_sub(1)
//             .map_or_else(|| 0, |v| v);
//         self.extra_mana = self
//             .extra_mana
//             .abs()
//             .checked_sub(1)
//             .map_or_else(|| 0, |v| v);
//         if 0 < self.extra_mana {
//             self.mana += 101;
//         }
//         let armor = if 0 < self.extra_armor { 7 } else { 0 };

//         if 0 < self.extra_damage {
//             if enemy.hit_point <= 3 {
//                 enemy.hit_point = 0;
//                 return;
//             } else {
//                 enemy.hit_point -= 3;
//             }
//         }

//         if enemy.damage <= armor {
//             if self.hit_point == 1 {
//                 self.hit_point = 0;
//                 return;
//             }
//             self.hit_point -= 1;
//         } else if self.hit_point + armor <= enemy.damage {
//             self.hit_point = 0;
//             return;
//         } else {
//             self.hit_point -= enemy.damage - armor;
//         }
//         self.extra_damage = self
//             .extra_damage
//             .abs()
//             .checked_sub(1)
//             .map_or_else(|| 0, |v| v);
//         self.extra_armor = self
//             .extra_armor
//             .abs()
//             .checked_sub(1)
//             .map_or_else(|| 0, |v| v);
//         self.extra_mana = self
//             .extra_mana
//             .abs()
//             .checked_sub(1)
//             .map_or_else(|| 0, |v| v);
//     }
// }

#[aoc(2015, 22)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        let hp = regex!(r"^Hit Points: ([0-9]+)$");
        let damage = regex!(r"^Damage: ([0-9]+)$");
        if let Ok(segment) = hp.captures(block).ok_or(ParseError) {
            self.hit_point = segment[1].parse::<usize>()?;
        }
        if let Ok(segment) = damage.captures(block).ok_or(ParseError) {
            self.damage = segment[1].parse::<usize>()?;
        }
        Ok(())
    }
    fn end_of_data(&mut self) {
        self.player.hit_point = self.hit_point;
        self.boss.hit_point = self.hit_point;
        self.player.damage = self.damage;
        self.boss.damage = self.damage;
    }
    fn part1(&mut self) -> Self::Output1 {
        0
    }
    fn part2(&mut self) -> Self::Output2 {
        0
    }
}
