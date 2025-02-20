//! <https://adventofcode.com/2016/day/14>
use {
    crate::framework::{aoc, AdventOfCode},
    md5::{Digest, Md5},
    std::collections::VecDeque,
};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<()>,
}

#[aoc(2016, 14)]
impl AdventOfCode for Puzzle {
    fn part1(&mut self) -> Self::Output1 {
        let limit = 64;
        let mut passed = 0;
        let mut queue: VecDeque<(String, Vec<char>)> = VecDeque::new();
        let salt = "ahsbgdzn";
        let mut hasher = Md5::new();
        // let salt = "abc";
        // let mut count = 0;
        for i in 0..1000 {
            hasher.update(format!("{salt}{i}"));
            let result = hasher.finalize_reset();
            let phrase = format!("{:x}", result);
            let occ5 = phrase
                .chars()
                .collect::<Vec<char>>()
                .windows(5)
                .filter(|s| s.iter().all(|c| *c == s[0]))
                .map(|s| s[0])
                .collect::<Vec<_>>();

            queue.push_back((phrase, occ5));
        }
        let mut check = 0;
        // let's start generate and check phase.
        'next_phrase: while passed < limit {
            // generate
            hasher.update(format!("{}{}", salt, check + 1000));
            let result = hasher.finalize_reset();
            let phrase = format!("{:x}", result);
            let occ5 = phrase
                .chars()
                .collect::<Vec<char>>()
                .windows(5)
                .filter(|s| s.iter().all(|c| *c == s[0]))
                .map(|s| s[0])
                .collect::<Vec<_>>();

            queue.push_back((phrase, occ5));
            check += 1;
            // check
            let phrase = queue.pop_front().unwrap();
            for s in phrase.0.chars().collect::<Vec<char>>().windows(3) {
                if s[0] == s[1] && s[0] == s[2] {
                    let ch = s[0];
                    if queue.iter().any(|(_, cs)| cs.contains(&ch)) {
                        passed += 1;
                        // println!("{:3>}, {:9>}: {:?}", passed, check - 1, phrase);
                        continue 'next_phrase;
                    }
                    break;
                }
            }
        }
        check - 1
    }
    #[allow(unused)]
    fn part2(&mut self) -> Self::Output2 {
        let limit = 64;
        let mut passed = 0;
        let mut queue: VecDeque<(String, Vec<char>)> = VecDeque::new();
        // let salt = "abc";
        let salt = "ahsbgdzn";
        let mut hasher = Md5::new();
        // let mut count = 0;
        for i in 0..1000 {
            hasher.update(format!("{salt}{i}"));
            let mut result = hasher.finalize_reset();
            {
                for _ in 0..2016 {
                    hasher.update(format!("{:x}", result));
                    result = hasher.finalize_reset();
                }
            }
            let phrase = format!("{:x}", result);
            let occ5 = phrase
                .chars()
                .collect::<Vec<char>>()
                .windows(5)
                .filter(|s| s.iter().all(|c| *c == s[0]))
                .map(|s| s[0])
                .collect::<Vec<_>>();
            queue.push_back((phrase, occ5));
        }
        let mut check = 0;
        // let's start generate and check phase.
        'next_phrase: while passed < limit {
            // generate
            hasher.update(format!("{}{}", salt, check + 1000));
            let mut result = hasher.finalize_reset();
            {
                for _ in 0..2016 {
                    hasher.update(format!("{:x}", result));
                    result = hasher.finalize_reset();
                }
            }
            let phrase = format!("{:x}", result);
            let occ5 = phrase
                .chars()
                .collect::<Vec<char>>()
                .windows(5)
                .filter(|s| s.iter().all(|c| *c == s[0]))
                .map(|s| s[0])
                .collect::<Vec<_>>();

            queue.push_back((phrase, occ5));
            check += 1;
            // check
            let phrase = queue.pop_front().unwrap();
            for s in phrase.0.chars().collect::<Vec<char>>().windows(3) {
                if s[0] == s[1] && s[0] == s[2] {
                    let ch = s[0];
                    if queue.iter().any(|(_, cs)| cs.contains(&ch)) {
                        passed += 1;
                        // println!("{:3>}, {:9>}: {:?}", passed, check - 1, phrase);
                        continue 'next_phrase;
                    }
                    break;
                }
            }
        }
        check - 1
    }
}
