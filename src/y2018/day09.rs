//! <https://adventofcode.com/2018/day/9>
use crate::framework::{aoc, AdventOfCode, ParseError};

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
        let mut current = 0;
        let mut next_ball = 1;
        let mut cached_ptr = 0;
        for e in (1..=self.players).cycle() {
            if next_ball % 23 == 0 {
                points[e - 1] += next_ball;
                let mut buffer = [0; 8];
                let mut count = 0;
                while cached_ptr != current || count < 8 {
                    count += 1;
                    buffer[count % 8] = cached_ptr;
                    cached_ptr = circle_ptr[cached_ptr];
                }
                let prev_of_delete = buffer[(count + 1) % 8];
                let deletion_target = buffer[(count + 2) % 8];
                // dbg!(count % 8, prev_of_delete, deletion_target, &buffer);
                points[e - 1] += deletion_target;
                circle_ptr[prev_of_delete] = circle_ptr[deletion_target];
                current = circle_ptr[prev_of_delete];
            } else {
                let ptr = circle_ptr[current];
                let next = circle_ptr[ptr];
                circle_ptr[next_ball] = next;
                circle_ptr[ptr] = next_ball;
                current = next_ball;
            }
            // println!("[{e}] {circle:?}");
            if self.points - 1 == next_ball {
                return *points.iter().max().unwrap();
            }
            // print!("[{e}] ({current}): ");
            // print_link(&circle_ptr);
            next_ball += 1;
        }
        0
    }
}

#[allow(dead_code)]
fn print_link(link: &[usize]) {
    let mut i = 0;
    print!("0 ");
    while link[i] != 0 {
        print!("{} ", link[i]);
        i = link[i];
    }
    println!();
}
