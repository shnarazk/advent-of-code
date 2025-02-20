//! <https://adventofcode.com/2020/day/25>
use crate::framework::{aoc_at, AdventOfCode, ParseError};

#[derive(Clone, Debug, Default)]
pub struct Puzzle {
    card: usize,
    door: usize,
}

#[aoc_at(2020, 25)]
impl AdventOfCode for Puzzle {
    type Output1 = usize;
    type Output2 = String;
    const DELIMITER: &'static str = "\n";
    fn parse_block(&mut self, block: &str) -> Result<(), ParseError> {
        if self.card == 0 {
            self.card = block.parse::<usize>().unwrap();
        } else {
            self.door = block.parse::<usize>().unwrap();
        }
        Ok(())
    }
    fn part1(&mut self) -> usize {
        day25(5764801, 17807724);
        day25(self.card, self.door)
    }
    fn part2(&mut self) -> Self::Output2 {
        "That's it!".to_string()
    }
}

fn day25(card_pubkey: usize, door_pubkey: usize) -> usize {
    let card_loop_size = determine_loop_size(card_pubkey);
    let door_loop_size = determine_loop_size(door_pubkey);

    let encryption_key_by_card = transform(card_loop_size, door_pubkey);
    let encryption_key_by_door = transform(door_loop_size, card_pubkey);
    // dbg!(encryption_key_by_card);
    // dbg!(encryption_key_by_door);

    debug_assert_eq!(encryption_key_by_card, encryption_key_by_door);

    encryption_key_by_card
}

fn transform(loop_size: usize, subject_number: usize) -> usize {
    let mut value = 1;
    for _ in 0..loop_size {
        value = (value * subject_number) % 20201227;
    }
    value
}

fn determine_loop_size(public_key: usize) -> usize {
    let mut value = 1;
    for i in 1.. {
        value = (value * 7) % 20201227;
        if value == public_key {
            return i;
        }
    }
    unreachable!()
}
