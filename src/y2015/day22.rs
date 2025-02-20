//! <https://adventofcode.com/2015/day/22>
use {
    crate::framework::{aoc, AdventOfCode, ParseError},
    std::{cmp::Reverse, collections::BinaryHeap},
};

type SpellProp = (usize, usize, (usize, usize, usize, usize));

// (hitpoint, damage, armor, mana)
const SPELL: [SpellProp; 5] = [
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
    Won(usize),
    Lose,
}

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Player {
    hit_point: usize,
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
}

impl Puzzle {
    // turn consists of your spell then boss's attack
    fn turn(&self, kind: usize, dec: usize) -> Result<Puzzle, GameState> {
        if 2000 < self.used_mana {
            return Err(GameState::Impossible);
        }
        let mut new_state = self.clone();
        let mut armor = 0;
        macro_rules! change_state {
            () => {
                new_state.player.hit_point = new_state
                    .player
                    .hit_point
                    .checked_sub(dec)
                    .ok_or(GameState::Lose)?;
                for (kind, _) in SPELL.iter().enumerate() {
                    if let Some(remain) = &mut new_state.player.state[kind] {
                        assert!(*remain != 0);
                        new_state.player.hit_point += SPELL[kind].2 .0;
                        new_state.boss.hit_point = new_state
                            .boss
                            .hit_point
                            .checked_sub(SPELL[kind].2 .1)
                            .ok_or(GameState::Won(new_state.used_mana))?;
                        armor += ((kind == 2) as usize) * SPELL[kind].2 .2;
                        new_state.player.mana += SPELL[kind].2 .3;
                        if 1 == *remain {
                            new_state.player.state[kind] = None;
                        } else {
                            *remain -= 1;
                        }
                    }
                }
            };
        }
        change_state!();
        if new_state.player.mana < SPELL[kind].0 || new_state.player.state[kind].is_some() {
            return Err(GameState::Impossible);
        }
        new_state.player.mana -= SPELL[kind].0;
        new_state.used_mana += SPELL[kind].0;
        new_state.player.state[kind] = Some(SPELL[kind].1);
        armor = 0;
        change_state!();
        // boss atack
        new_state.player.hit_point = (new_state.player.hit_point + armor)
            .checked_sub(new_state.boss.damage)
            .ok_or(GameState::Lose)?;
        Ok(new_state)
    }
}

mod parser {
    use {
        crate::parser::parse_usize,
        winnow::{combinator::seq, ModalResult, Parser},
    };

    pub fn parse(s: &mut &str) -> ModalResult<(usize, usize)> {
        seq!(_: "Hit Points: ", parse_usize, _: "\nDamage: ", parse_usize).parse_next(s)
    }
}

#[aoc(2015, 22)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, mut input: &str) -> Result<(), ParseError> {
        let (hp, damage) = parser::parse(&mut input)?;
        self.boss.hit_point = hp;
        self.boss.damage = damage;
        Self::parsed()
    }
    fn end_of_data(&mut self) {
        self.player.hit_point = 49;
        self.player.mana = 500;
        self.boss.hit_point -= 1;
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut to_visit: BinaryHeap<Reverse<Puzzle>> = BinaryHeap::new();
        to_visit.push(Reverse(self.clone()));
        while let Some(Reverse(w)) = to_visit.pop() {
            for (i, _) in SPELL.iter().enumerate() {
                match w.turn(i, 0) {
                    Ok(ww) => to_visit.push(Reverse(ww)),
                    Err(GameState::Won(mana)) => {
                        return mana;
                    }
                    Err(GameState::Impossible) | Err(GameState::Lose) => continue,
                }
            }
        }
        unreachable!()
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut to_visit: BinaryHeap<Reverse<Puzzle>> = BinaryHeap::new();
        to_visit.push(Reverse(self.clone()));
        while let Some(Reverse(w)) = to_visit.pop() {
            for (i, _) in SPELL.iter().enumerate() {
                match w.turn(i, 1) {
                    Ok(ww) => to_visit.push(Reverse(ww)),
                    Err(GameState::Won(mana)) => {
                        return mana;
                    }
                    Err(GameState::Impossible) | Err(GameState::Lose) => continue,
                }
            }
        }
        unreachable!()
    }
}
