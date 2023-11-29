//! <https://adventofcode.com/2015/day/22>
use crate::{
    framework::{aoc, AdventOfCode, ParseError},
    regex,
};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct State {
    hit_point: usize,
    damage: usize,
    mana: usize,
    extra_damage: isize,
    extra_armor: isize,
    extra_mana: isize,
    used_mana: usize,
    born: bool,
    id: usize,
    pre: usize,
}

impl State {
    fn spell(&self, kind: usize) -> Option<State> {
        let mut s = self.clone();
        s.born = true;
        // your turn
        match kind {
            // Magic Missile
            1 if 53 <= s.mana => {
                s.damage = 4;
                s.mana -= 53;
                s.used_mana += 53;
            }
            // Drain
            2 if 73 <= s.mana => {
                s.damage = 2;
                s.hit_point += 2;
                s.mana -= 73;
                s.used_mana += 73;
            }
            // Shield
            3 if 113 <= s.mana && s.extra_armor == 0 => {
                s.extra_armor = -6 - 1;
                s.mana -= 113;
                s.used_mana += 113;
            }
            3 if 113 <= s.mana && s.extra_armor == 1 => {
                s.extra_armor = 7;
                s.mana -= 113;
                s.used_mana += 113;
            }
            // Poison
            4 if 173 <= s.mana && s.extra_damage == 0 => {
                s.extra_damage = -6 - 1;
                s.mana -= 173;
                s.used_mana += 173;
            }
            4 if 173 <= s.mana && s.extra_damage == 1 => {
                s.extra_damage = 7;
                s.mana -= 173;
                s.used_mana += 173;
            }
            // Shield
            5 if 229 <= s.mana && s.extra_mana == 0 => {
                s.extra_mana = -5 - 1;
                s.mana -= 229;
                s.used_mana += 229;
            }
            5 if 229 <= s.mana && s.extra_mana == 1 => {
                s.extra_mana = 6;
                s.mana -= 229;
                s.used_mana += 229;
            }
            _ => {
                return None;
            }
        }
        Some(s)
    }
    fn turn(&mut self, enemy: &mut State) {
        assert!(0 < enemy.hit_point);
        if 0 < self.extra_mana {
            self.mana += 101;
        }
        let damage = if 0 < self.extra_damage {
            self.damage + 3
        } else {
            self.damage
        };
        if enemy.hit_point <= damage {
            enemy.hit_point = 0;
            return;
        } else {
            enemy.hit_point -= damage;
        }
        self.damage = 0;
        // enemy turn
        self.extra_damage = self
            .extra_damage
            .abs()
            .checked_sub(1)
            .map_or_else(|| 0, |v| v);
        self.extra_armor = self
            .extra_armor
            .abs()
            .checked_sub(1)
            .map_or_else(|| 0, |v| v);
        self.extra_mana = self
            .extra_mana
            .abs()
            .checked_sub(1)
            .map_or_else(|| 0, |v| v);
        if 0 < self.extra_mana {
            self.mana += 101;
        }
        let armor = if 0 < self.extra_armor { 7 } else { 0 };

        if 0 < self.extra_damage {
            if enemy.hit_point <= 3 {
                enemy.hit_point = 0;
                return;
            } else {
                enemy.hit_point -= 3;
            }
        }

        if enemy.damage <= armor {
            if self.hit_point == 1 {
                self.hit_point = 0;
                return;
            }
            self.hit_point -= 1;
        } else if self.hit_point + armor <= enemy.damage {
            self.hit_point = 0;
            return;
        } else {
            self.hit_point -= enemy.damage - armor;
        }
        self.extra_damage = self
            .extra_damage
            .abs()
            .checked_sub(1)
            .map_or_else(|| 0, |v| v);
        self.extra_armor = self
            .extra_armor
            .abs()
            .checked_sub(1)
            .map_or_else(|| 0, |v| v);
        self.extra_mana = self
            .extra_mana
            .abs()
            .checked_sub(1)
            .map_or_else(|| 0, |v| v);
    }
    fn turn2(&mut self, enemy: &mut State) {
        assert!(0 < enemy.hit_point);
        if 0 < self.hit_point {
            self.hit_point -= 1;
        } else {
            self.hit_point = 0;
            return;
        }
        if 0 < self.extra_mana {
            self.mana += 101;
        }
        let damage = if 0 < self.extra_damage {
            self.damage + 3
        } else {
            self.damage
        };
        if enemy.hit_point <= damage {
            enemy.hit_point = 0;
            return;
        } else {
            enemy.hit_point -= damage;
        }
        self.damage = 0;
        // enemy turn
        if 0 < self.hit_point {
            self.hit_point -= 1;
        } else {
            self.hit_point = 0;
            return;
        }
        self.extra_damage = self
            .extra_damage
            .abs()
            .checked_sub(1)
            .map_or_else(|| 0, |v| v);
        self.extra_armor = self
            .extra_armor
            .abs()
            .checked_sub(1)
            .map_or_else(|| 0, |v| v);
        self.extra_mana = self
            .extra_mana
            .abs()
            .checked_sub(1)
            .map_or_else(|| 0, |v| v);
        if 0 < self.extra_mana {
            self.mana += 101;
        }
        let armor = if 0 < self.extra_armor { 7 } else { 0 };

        if 0 < self.extra_damage {
            if enemy.hit_point <= 3 {
                enemy.hit_point = 0;
                return;
            } else {
                enemy.hit_point -= 3;
            }
        }

        if enemy.damage <= armor {
            if self.hit_point == 1 {
                self.hit_point = 0;
                return;
            }
            self.hit_point -= 1;
        } else if self.hit_point + armor <= enemy.damage {
            self.hit_point = 0;
            return;
        } else {
            self.hit_point -= enemy.damage - armor;
        }
        self.extra_damage = self
            .extra_damage
            .abs()
            .checked_sub(1)
            .map_or_else(|| 0, |v| v);
        self.extra_armor = self
            .extra_armor
            .abs()
            .checked_sub(1)
            .map_or_else(|| 0, |v| v);
        self.extra_mana = self
            .extra_mana
            .abs()
            .checked_sub(1)
            .map_or_else(|| 0, |v| v);
    }
}

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    hit_point: usize,
    damage: usize,
}

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
    fn wrap_up(&mut self) {
        dbg!(&self);
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut sid: usize = 0;
        let mut bag: Vec<(State, State)> = vec![(
            State {
                hit_point: 50,
                mana: 500,
                born: true,
                ..State::default()
            },
            State {
                hit_point: 58,
                damage: 9,
                ..State::default()
            },
        )];
        while let Some(s) = bag
            .iter_mut()
            .filter(|s| s.0.born)
            .min_by_key(|s| s.0.used_mana)
        {
            // dbg!(&s);
            s.0.born = false;
            let parent = s.0.id;
            let state = s.clone();
            // bag.retain(|t| state != *t);
            if state.1.hit_point == 0 {
                let mut target = s.0.id;
                while target != 0 {
                    let s = bag.iter().find(|s| s.0.id == target).unwrap();
                    println!(
                        "[{}H, {}A, {}M, {}U] : [{}H]",
                        s.0.hit_point,
                        if 0 < s.0.extra_armor { 7 } else { 0 },
                        s.0.mana,
                        s.0.used_mana,
                        s.1.hit_point,
                    );
                    target = s.0.pre;
                }
                return state.0.used_mana;
            }
            if state.0.hit_point == 0 {
                continue;
            }
            for i in 1..=5 {
                if let Some(mut n) = state.0.spell(i) {
                    let mut enemy = state.1.clone();
                    n.turn(&mut enemy);
                    sid += 1;
                    n.id = sid;
                    n.pre = parent;
                    bag.push((n, enemy));
                }
            }
        }
        0
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut sid: usize = 0;
        let mut bag: Vec<(State, State)> = vec![(
            State {
                hit_point: 50,
                mana: 500,
                born: true,
                ..State::default()
            },
            State {
                hit_point: 58,
                damage: 9,
                ..State::default()
            },
        )];
        while let Some(s) = bag
            .iter_mut()
            .filter(|s| s.0.born)
            .min_by_key(|s| s.0.used_mana)
        {
            // dbg!(&s);
            s.0.born = false;
            let parent = s.0.id;
            let state = s.clone();
            // bag.retain(|t| state != *t);
            if state.1.hit_point == 0 {
                let mut target = s.0.id;
                while target != 0 {
                    let s = bag.iter().find(|s| s.0.id == target).unwrap();
                    println!(
                        "[{}H, {}A, {}M, {}U] : [{}H]",
                        s.0.hit_point,
                        if 0 < s.0.extra_armor { 7 } else { 0 },
                        s.0.mana,
                        s.0.used_mana,
                        s.1.hit_point,
                    );
                    target = s.0.pre;
                }
                return state.0.used_mana;
            }
            if state.0.hit_point == 0 {
                continue;
            }
            for i in 1..=5 {
                if let Some(mut n) = state.0.spell(i) {
                    let mut enemy = state.1.clone();
                    n.turn2(&mut enemy);
                    sid += 1;
                    n.id = sid;
                    n.pre = parent;
                    bag.push((n, enemy));
                }
            }
        }
        0
    }
}
