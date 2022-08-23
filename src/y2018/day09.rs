//! <https://adventofcode.com/2018/day/9>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::framework::{aoc, AdventOfCode, ParseError},
    std::collections::HashMap,
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    players: usize,
    points: usize,
}

#[aoc(2018, 9)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, _block: &str) -> Result<(), ParseError> {
        Ok(())
    }
    fn after_insert(&mut self) {
        // 410 players; last marble is worth 72059 points
        self.players = 410;
        self.points = 72059;
        // self.players = 13;
        // self.points = 7999;
        // self.players = 10;
        // self.points = 1618;
        // self.players = 9;
        // self.points = 25;
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut points = Vec::new();
        points.resize(self.players, 0);
        let mut circle = vec![0];
        let mut current = 1;
        let mut next_ball = 1;
        for e in (1..=self.players).cycle() {
            let len = circle.len();
            if len == 0 {
                circle.push(next_ball);
                next_ball += 1;
                // println!("[{e}] {circle:?}");
                continue;
            }
            if next_ball % 23 == 0 {
                points[e - 1] += next_ball;
                current = (len + current - 7) % len;
                points[e - 1] += circle[current];
                circle.remove(current);
            } else {
                current = (current + 1) % len + 1;
                circle.insert(current, next_ball);
            }
            // println!("[{e}] {circle:?}");
            if self.points == next_ball {
                return *points.iter().max().unwrap();
            }
            next_ball += 1;
        }
        0
    }
    fn part2(&mut self) -> Self::Output2 {
        self.points *= 100;
        // self.players = 10;
        // self.points = 1618;
        let mut points = Vec::new();
        points.resize(self.players, 0);
        let mut circle_ptr = Vec::new();
        circle_ptr.resize(self.points, 0);
        let mut circle_len = 1;
        let mut current = 0;
        let mut next_ball = 1;
        for e in (1..=self.players).cycle() {
            // if circle_len == 0 {
            //     next_ball += 1;
            //     circle_len += 1;
            //     continue;
            // }
            if next_ball % 23 == 0 {
                points[e - 1] += next_ball;
                // current = (circle_len + current - 7) % circle_len;
                let mut ptr = 0;
                let mut buffer = [0; 8];
                let mut count = 0;
                while ptr != current || count < 8 {
                    count += 1;
                    buffer[count % 8] = ptr;
                    ptr = circle_ptr[ptr];
                }
                assert!(7 < count);
                let prev_of_delete = buffer[(count + 1) % 8];
                let deletion_target = buffer[(count + 2) % 8];
                // dbg!(count % 8, prev_of_delete, deletion_target, &buffer);
                points[e - 1] += deletion_target;
                circle_ptr[prev_of_delete] = circle_ptr[deletion_target];
                current = circle_ptr[prev_of_delete];
                circle_len -= 1;
            } else {
                // current = (current + 2) % circle_len + 1;
                let ptr = circle_ptr[current];
                let next = circle_ptr[ptr];
                circle_ptr[next_ball] = next;
                // if ptr == 0 && 1 < circle_len {
                //     ptr = circle_len;
                // }
                circle_ptr[ptr] = next_ball;
                current = next_ball;
                circle_len += 1;
            }
            // println!("[{e}] {circle:?}");
            if self.points - 1 == next_ball {
                dbg!();
                return *points.iter().max().unwrap();
            }
            // print!("[{e}] ({current}): ");
            // print_link(&circle_ptr);
            next_ball += 1;
        }
        0
    }
}

fn print_link(link: &[usize]) {
    let mut i = 0;
    print!("0 ");
    while link[i] != 0 {
        print!("{} ", link[i]);
        i = link[i];
    }
    println!();
}
