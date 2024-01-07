//! <https://adventofcode.com/2015/day/22>
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        regex,
    },
    std::{cmp::Reverse, collections::BinaryHeap},
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
    used_mana: usize,
    player: Player,
    boss: Boss,
    hit_point: usize,
    damage: usize,
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
        new_state.used_mana -= SPELL[kind].0;
        let mut armor = 0;
        // your spell effects just before the boss's turn
        for (kind, _) in SPELL.iter().enumerate() {
            if let Some(remain) = &mut new_state.player.state[kind] {
                if 0 == *remain {
                    new_state.player.state[kind] = None;
                } else {
                    *remain -= 1;
                    new_state.player.hit_point += SPELL[kind].2 .0;
                    new_state.boss.hit_point = new_state
                        .boss
                        .hit_point
                        .checked_sub(SPELL[kind].2 .1)
                        .ok_or(GameState::Won)?;
                    armor += SPELL[kind].2 .2;
                    new_state.player.mana += SPELL[kind].2 .3;
                }
            }
        }
        // boss atack
        new_state.player.hit_point = (new_state.player.hit_point + 7 * armor)
            .checked_sub(new_state.boss.damage)
            .ok_or(GameState::Lose)?;
        Ok(new_state)
    }
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
    fn end_of_data(&mut self) {
        self.player.hit_point = 50 - 1;
        self.player.mana = 500;
        self.boss.hit_point = self.hit_point - 1;
        self.boss.damage = self.damage;
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut to_visit: BinaryHeap<Reverse<Puzzle>> = BinaryHeap::new();
        to_visit.push(Reverse(self.clone()));
        while let Some(Reverse(w)) = to_visit.pop() {
            for (i, _) in SPELL.iter().enumerate() {
                match w.turn(i) {
                    Ok(ww) => to_visit.push(Reverse(ww)),
                    Err(GameState::Won) => return w.used_mana,
                    Err(GameState::Impossible) | Err(GameState::Lose) => continue,
                }
            }
        }
        unreachable!();
    }
    fn part2(&mut self) -> Self::Output2 {
        0
    }
}
