//! <https://adventofcode.com/2019/day/24>
use {
    crate::framework::{AdventOfCode, ParseError, aoc},
    std::collections::{HashMap, HashSet},
};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Vec<bool>>,
}

#[aoc(2019, 24)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, input: &str) -> Result<(), ParseError> {
        self.line = input
            .lines()
            .map(|line| line.chars().map(|c| c == '#').collect())
            .collect();
        Self::parsed()
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut visited: HashSet<u32> = HashSet::new();
        let mut state: u32 = self.to_u32();
        loop {
            let mut new_state: u32 = state;
            for i in 0..25 {
                let mut neighbors = 0;
                if 4 < i {
                    neighbors += (0 != (state & (1 << (i - 5)))) as u32;
                }
                if i < 20 {
                    neighbors += (0 != (state & (1 << (i + 5)))) as u32;
                }
                if 0 < i && i % 5 != 0 {
                    neighbors += (0 != (state & (1 << (i - 1)))) as u32;
                }
                if i < 24 && i % 5 != 4 {
                    neighbors += (0 != (state & (1 << (i + 1)))) as u32;
                }
                match (0 != state & (1 << i), neighbors) {
                    (true, n) if n != 1 => new_state &= !(1 << i),
                    (false, 1) | (false, 2) => new_state |= 1 << i,
                    _ => (),
                }
            }
            if visited.contains(&new_state) {
                // dump(state);
                return new_state as usize;
            }
            visited.insert(new_state);
            state = new_state;
        }
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut state: HashMap<i32, u32> = HashMap::new();
        state.insert(0, self.to_u32());
        state.insert(1, 0);
        state.insert(-1, 0);
        let mut plane = Plane { state };
        // plane.dump(0);
        for _ in 0..200 {
            plane = plane.proceed();
            // plane.dump(0);
            // println!();
        }
        // plane.dump(0);
        plane.bugs()
    }
}

impl Puzzle {
    fn to_u32(&self) -> u32 {
        let mut code: u32 = 0;
        let mut radix: u32 = 1;
        for l in self.line.iter() {
            for b in l.iter() {
                code += radix * (*b as u32);
                radix *= 2;
            }
        }
        code
    }
}

#[allow(dead_code)]
fn dump(state: u32) {
    for i in 0..25 {
        print!(
            "{}{}",
            if 0 != (state & (1 << i)) { '#' } else { '.' },
            if i % 5 == 4 { '\n' } else { ' ' },
        )
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct Plane {
    state: HashMap<i32, u32>,
}

impl Plane {
    #[allow(dead_code)]
    fn dump(&self, level: i32) {
        if let Some(state) = self.state.get(&level) {
            for i in 0..25 {
                print!(
                    "{}{}",
                    if 0 != (state & (1 << i)) { '#' } else { '.' },
                    if i % 5 == 4 { '\n' } else { ' ' },
                )
            }
        }
    }
    fn bugs(&self) -> usize {
        let mut num = 0;
        for level in self.state.keys() {
            num += self.bugs_at(*level);
        }
        num
    }
    fn bugs_at(&self, level: i32) -> usize {
        if let Some(state) = self.state.get(&level) {
            (0..25).filter(|i| 0 != (state & (1 << i))).count()
        } else {
            0
        }
    }
    fn proceed(&self) -> Plane {
        let mut next_state = (*self).clone();
        self.update_ring(0, &mut next_state);
        for i in -200..200 {
            if 0 < self.bugs_at(i) || self.shrinking(i - 1) || self.extending(i + 1) {
                self.update_ring(i, &mut next_state);
            }
        }
        next_state
    }
    fn update_ring(&self, level: i32, next: &mut Plane) {
        let join = [
            // 1st row
            vec![(-1, 7), (0, 1), (0, 5), (-1, 11)],
            vec![(-1, 7), (0, 2), (0, 6), (0, 0)],
            vec![(-1, 7), (0, 3), (0, 7), (0, 1)],
            vec![(-1, 7), (0, 4), (0, 8), (0, 2)],
            vec![(-1, 7), (-1, 13), (0, 9), (0, 3)],
            // 2nd row
            vec![(0, 0), (0, 6), (0, 10), (-1, 11)],
            vec![(0, 1), (0, 7), (0, 11), (0, 5)],
            vec![
                (0, 2),
                (0, 8),
                (1, 0),
                (1, 1),
                (1, 2),
                (1, 3),
                (1, 4),
                (0, 6),
            ],
            vec![(0, 3), (0, 9), (0, 13), (0, 7)],
            vec![(0, 4), (-1, 13), (0, 14), (0, 8)],
            // 3rd row
            vec![(0, 5), (0, 11), (0, 15), (-1, 11)],
            vec![
                (0, 6),
                (1, 0),
                (1, 5),
                (1, 10),
                (1, 15),
                (1, 20),
                (0, 16),
                (0, 10),
            ],
            vec![],
            vec![
                (0, 8),
                (0, 14),
                (0, 18),
                (1, 4),
                (1, 9),
                (1, 14),
                (1, 19),
                (1, 24),
            ],
            vec![(0, 9), (-1, 13), (0, 19), (0, 13)],
            // 4th row
            vec![(0, 10), (0, 16), (0, 20), (-1, 11)],
            vec![(0, 11), (0, 17), (0, 21), (0, 15)],
            vec![
                (1, 20),
                (1, 21),
                (1, 22),
                (1, 23),
                (1, 24),
                (0, 18),
                (0, 22),
                (0, 16),
            ],
            vec![(0, 13), (0, 19), (0, 23), (0, 17)],
            vec![(0, 14), (-1, 13), (0, 24), (0, 18)],
            // last row
            vec![(0, 15), (0, 21), (-1, 17), (-1, 11)],
            vec![(0, 16), (0, 22), (-1, 17), (0, 20)],
            vec![(0, 17), (0, 23), (-1, 17), (0, 21)],
            vec![(0, 18), (0, 24), (-1, 17), (0, 22)],
            vec![(0, 19), (-1, 13), (-1, 17), (0, 23)],
        ];
        let plane = *self.state.get(&level).unwrap_or(&0);
        let inner = *self.state.get(&(level + 1)).unwrap_or(&0);
        let outer = *self.state.get(&(level - 1)).unwrap_or(&0);
        let mut new_state: u32 = plane;
        for (i, neighbors) in join.iter().enumerate() {
            let nn = neighbors
                .iter()
                .filter(|(level, ii)| {
                    0 != match level {
                        1 => inner,
                        -1 => outer,
                        _ => plane,
                    } & (1 << ii)
                })
                .count();
            match (0 != plane & (1 << i), nn) {
                _ if i == 12 => (),
                (true, n) if n != 1 => new_state &= !(1 << i),
                (false, 1) | (false, 2) => new_state |= 1 << i,
                _ => (),
            }
        }
        next.state.insert(level, new_state);
    }
    fn extending(&self, level: i32) -> bool {
        self.state.get(&level).is_some_and(|state| {
            [0, 1, 2, 3, 4, 5, 9, 10, 14, 15, 19, 20, 21, 22, 23, 24]
                .iter()
                .any(|i| 0 != state & (1 << i))
        })
    }
    fn shrinking(&self, level: i32) -> bool {
        self.state
            .get(&level)
            .is_some_and(|state| [7, 11, 13, 17].iter().any(|i| 0 != state & (1 << i)))
    }
}
