//! <https://adventofcode.com/2020/day/25>
use crate::framework::{aoc_at, AdventOfCode, Description, ParseError};

#[derive(Debug, Default)]
pub struct Puzzle {}

#[aoc_at(2020, 25)]
impl AdventOfCode for Puzzle {
    type Output1 = usize;
    type Output2 = String;
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, _block: &str) -> Result<(), ParseError> {
        Ok(())
    }
    fn part1(&mut self) -> usize {
        day25(0, Description::TestData("".to_string()));
        day25(0, Description::None)
    }
    fn part2(&mut self) -> Self::Output2 {
        "That's it!".to_string()
    }
}

fn day25(_: usize, tag: Description) -> usize {
    if let Description::TestData(_) = tag {
        let card_pubkey = 5764801;
        let door_pubkey = 17807724;
        assert_eq!(transform(8, 7), card_pubkey);
        assert_eq!(transform(11, 7), door_pubkey);

        let card_loop_size = determine_loop_size(card_pubkey);
        let door_loop_size = determine_loop_size(door_pubkey);

        let encryption_key_by_card = transform(card_loop_size, door_pubkey);
        let encryption_key_by_door = transform(door_loop_size, card_pubkey);
        dbg!(encryption_key_by_card);
        dbg!(encryption_key_by_door);

        assert_eq!(encryption_key_by_card, encryption_key_by_door);

        encryption_key_by_card
    } else {
        let card_pubkey = 12320657;
        let door_pubkey = 9659666;
        let card_loop_size = determine_loop_size(card_pubkey);
        let door_loop_size = determine_loop_size(door_pubkey);
        assert_eq!(transform(card_loop_size, 7), card_pubkey);
        assert_eq!(transform(door_loop_size, 7), door_pubkey);

        let encryption_key_by_card = transform(card_loop_size, door_pubkey);
        let encryption_key_by_door = transform(door_loop_size, card_pubkey);
        dbg!(encryption_key_by_card);
        dbg!(encryption_key_by_door);

        assert_eq!(encryption_key_by_card, encryption_key_by_door);

        encryption_key_by_card
    }
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
    0
}
