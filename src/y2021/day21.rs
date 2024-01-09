//! <https://adventofcode.com/2021/day/21>
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        progress, regex,
    },
    std::collections::HashMap,
};

#[derive(Debug, Default)]
pub struct Puzzle {
    line: Vec<usize>,
}

#[aoc(2021, 21)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        let parser = regex!(r"^Player ([0-9]+) starting position: ([0-9]+)$");
        let segment = parser.captures(block).ok_or(ParseError)?;
        self.line.push(segment[2].parse::<usize>()?);
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut pos: [usize; 2] = [self.line[0], self.line[1]];
        let mut score: [usize; 2] = [0, 0];
        let mut dices = 0;
        let mut current_dice = 0;
        let mut turn = 0;
        while score[0].max(score[1]) < 1000 {
            let mut step = 0;
            current_dice = current_dice % 100 + 1;
            step += current_dice;
            current_dice = current_dice % 100 + 1;
            step += current_dice;
            current_dice = current_dice % 100 + 1;
            step += current_dice;
            let t = (turn % 2) as usize;
            pos[t] = (pos[t] + step - 1) % 10 + 1;
            score[t] += pos[t];
            dices += 3;
            turn += 1;
            progress!(format!(
                "turn {}, dice {}, step {}, pos {} score{:?}",
                turn, current_dice, step, pos[t], &score
            ));
        }
        progress!("");
        score[0].min(score[1]) * dices
    }
    fn part2(&mut self) -> Self::Output2 {
        // (pos, score), (pos, score), turn => the number of universes
        let mut scores: HashMap<(usize, usize, usize, usize, bool), usize> = HashMap::new();
        let mut next: HashMap<(usize, usize, usize, usize, bool), usize> = HashMap::new();
        let mut universes: (usize, usize) = (0, 0);
        scores.insert((self.line[0], 0, self.line[1], 0, false), 1); // false means the next turn is player 0.
        while !scores.is_empty() {
            for (key, count) in scores.iter() {
                let k = *key;
                let c = *count;
                if 21 <= k.1 {
                    universes.0 += c;
                    continue;
                }
                if 21 <= k.3 {
                    universes.1 += c;
                    continue;
                }
                // generate new universes
                // 3: 1:: (1, 1, 1)
                // 4: 3:: (1, 1, 2), (1, 2, 1), (2, 1, 1)
                // 5: 6:: (1, 2, 2), (2, 1, 2), (2, 2, 1), (1, 1, 3), (1, 3, 1), (3, 1, 1)
                // 6: 7:: (1, 2, 3), (1, 3, 2), (2, 1, 3), (2, 3, 1), (3, 1, 2), (3, 2, 1), (2, 2, 2)
                // 7: 6:: (1, 2, 2), (2, 1, 2), (2, 2, 1), (1, 1, 3), (1, 3, 1), (3, 1, 1)
                // 8: 3:: (3, 3, 2), (3, 2, 3), (2, 3, 3)
                // 9: 1:: (3, 3, 3)
                if k.4 {
                    // player 1
                    let (pos, score) = (k.2, k.3);
                    for i in 3..=9 {
                        let new_pos = (pos + i - 1) % 10 + 1;
                        debug_assert!(0 < new_pos && new_pos <= 10, "{}", new_pos);
                        let new_score = score + new_pos;
                        let n = match i {
                            3 | 9 => 1,
                            4 | 8 => 3,
                            5 | 7 => 6,
                            _ => 7,
                        };
                        *next
                            .entry((k.0, k.1, new_pos, new_score, false))
                            .or_default() += n * c;
                    }
                } else {
                    // player 0
                    let (pos, score) = (k.0, k.1);
                    for i in 3..=9 {
                        let new_pos = (pos + i - 1) % 10 + 1;
                        debug_assert!(0 < new_pos && new_pos <= 10, "{}", new_pos);
                        let new_score = score + new_pos;
                        let n = match i {
                            3 | 9 => 1,
                            4 | 8 => 3,
                            5 | 7 => 6,
                            _ => 7,
                        };
                        *next
                            .entry((new_pos, new_score, k.2, k.3, true))
                            .or_default() += n * c;
                    }
                }
            }
            scores.clear();
            std::mem::swap(&mut scores, &mut next);
        }
        universes.0.max(universes.1)
    }
}
