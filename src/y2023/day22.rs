//! <https://adventofcode.com/2023/day/22>
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::Dim3,
        line_parser,
    },
    std::{
        cmp::Ordering,
        collections::{HashMap, HashSet},
    },
};

#[derive(Debug, Default, Eq, Hash, PartialEq)]
struct Block {
    pos: Dim3<usize>,
    shape: Dim3<usize>,
}

impl PartialOrd for Block {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        let my_range_x = (self.pos.0, self.pos.0 + self.shape.0);
        let my_range_y = (self.pos.1, self.pos.1 + self.shape.1);
        let other_range_x = (other.pos.0, other.pos.0 + other.shape.0);
        let other_range_y = (other.pos.1, other.pos.1 + other.shape.1);
        if (if my_range_y.0 <= other_range_y.0 {
            my_range_y.1 >= other_range_y.0
        } else {
            other_range_y.1 >= my_range_y.0
        }) && (if my_range_x.0 <= other_range_x.0 {
            my_range_x.1 >= other_range_x.0
        } else {
            other_range_x.1 >= my_range_x.0
        }) {
            if self.pos.2 + self.shape.2 < other.pos.2 {
                return Some(Ordering::Less);
            } else if other.pos.2 + other.shape.2 < self.pos.2 {
                return Some(Ordering::Greater);
            }
        }
        None
    }
}

#[derive(Debug, Default, Eq, PartialEq)]
pub struct Puzzle {
    blocks: Vec<Block>,
    supported: Vec<Vec<usize>>,
    supporting: HashMap<usize, Vec<usize>>,
}

#[aoc(2023, 22)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        let v = block
            .split('~')
            .map(|s| line_parser::to_usizes(s, ',').unwrap())
            .map(|v| (v[0], v[1], v[2]))
            .collect::<Vec<_>>();
        debug_assert!(v[0].0 <= v[1].0 && v[0].1 <= v[1].1 && v[0].2 <= v[1].2);
        let blk = Block {
            pos: v[0],
            shape: (v[1].0 - v[0].0, v[1].1 - v[0].1, v[1].2 - v[0].2),
        };
        self.blocks.push(blk);
        Ok(())
    }
    fn end_of_data(&mut self) {
        stabilize(&mut self.blocks);
        self.supported = (0..self.blocks.len())
            .map(|i| {
                let mut v = (0..self.blocks.len())
                    .filter(|j| {
                        self.blocks[*j].partial_cmp(&self.blocks[i]) == Some(Ordering::Less)
                    })
                    .map(|j| (self.blocks[j].pos.2 + self.blocks[j].shape.2, j))
                    .collect::<Vec<_>>();
                v.sort();
                v.reverse();
                let Some((l, _)) = v.first() else {
                    return Vec::new();
                };
                v.iter()
                    .filter(|(level, _)| *level == *l)
                    .map(|(_, j)| *j)
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
    }
    fn part1(&mut self) -> Self::Output1 {
        (0..self.blocks.len())
            .filter(|i| self.supported.iter().all(|v| !v.contains(i) || 1 < v.len()))
            .count()
    }
    fn part2(&mut self) -> Self::Output1 {
        for (i, v) in self.supported.iter().enumerate() {
            for j in v.iter() {
                self.supporting.entry(*j).or_default().push(i);
            }
        }

        (0..self.blocks.len())
            .filter(|i| !self.supported.iter().all(|v| !v.contains(i) || 1 < v.len()))
            .map(|i| self.chain_len(i))
            .sum()
    }
}

fn stabilize(blocks: &mut [Block]) {
    while (0..blocks.len()).any(|i| move_down(blocks, i)) {}
}

fn move_down(blocks: &mut [Block], i: usize) -> bool {
    let level = blocks
        .iter()
        .enumerate()
        .filter(|(_, other)| Some(Ordering::Less) == (*other).partial_cmp(&blocks[i]))
        .map(|(_, other)| other.pos.2 + other.shape.2 + 1)
        .max()
        .unwrap_or(1);
    if level < blocks[i].pos.2 {
        blocks[i].pos.2 = level;
        return true;
    }
    false
}

impl Puzzle {
    fn chain_len(&self, start: usize) -> usize {
        let mut blacklist: HashSet<usize> = HashSet::new();
        blacklist.insert(start);
        let mut to_visit: Vec<usize> = vec![start];
        while let Some(i) = to_visit.pop() {
            for to in self.supporting.get(&i).unwrap_or(&vec![]) {
                if self.supported[*to]
                    .iter()
                    .filter(|s| !blacklist.contains(*s))
                    .count()
                    == 0
                {
                    blacklist.insert(*to);
                    to_visit.push(*to);
                }
            }
        }
        blacklist.len() - 1
    }
}
