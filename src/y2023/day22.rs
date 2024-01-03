//! <https://adventofcode.com/2023/day/22>
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::Dim3,
        line_parser,
    },
    std::{cmp::Ordering, collections::HashMap},
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
                let v = (0..self.blocks.len())
                    .filter(|j| {
                        self.blocks[*j].partial_cmp(&self.blocks[i]) == Some(Ordering::Less)
                    })
                    .map(|j| (self.blocks[j].pos.2 + self.blocks[j].shape.2, j))
                    .collect::<Vec<_>>();
                let Some((l, _)) = v.iter().max() else {
                    return Vec::new();
                };
                v.iter()
                    .filter(|(level, _)| *level == *l)
                    .map(|(_, j)| *j)
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
    }
    fn serialize(&self) -> Option<String> {
        serde_json::to_string(&self.supported).ok()
    }
    fn part1(&mut self) -> Self::Output1 {
        (0..self.blocks.len())
            .filter(|i| self.supported.iter().all(|v| !v.contains(i) || 1 < v.len()))
            .count()
    }
    fn part2(&mut self) -> Self::Output1 {
        self.build_colapse_map().values().map(|l| l.len()).sum()
    }
}

fn stabilize(blocks: &mut [Block]) {
    blocks.sort_by_key(|b| b.pos.2);
    for i in 0..blocks.len() {
        move_down(blocks, i);
    }
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
    fn build_colapse_map(&self) -> HashMap<usize, Vec<usize>> {
        let mut hash: HashMap<usize, Vec<usize>> = HashMap::new();
        for n in 0..self.blocks.len() {
            let _ = self.colapsed_by(n, &mut hash);
        }
        hash
    }
    fn colapsed_by(&self, start: usize, memo: &mut HashMap<usize, Vec<usize>>) -> Vec<usize> {
        if let Some(l) = memo.get(&start) {
            return l.clone();
        }
        let supported = &self.supported[start];
        let path = match supported.len() {
            0 => Vec::new(),
            1 => {
                let mut p = self.colapsed_by(supported[0], memo);
                p.push(supported[0]);
                p
            }
            _ => {
                let cands = supported
                    .iter()
                    .map(|c| self.colapsed_by(*c, memo))
                    .collect::<Vec<_>>();
                let len = cands.iter().map(|l| l.len()).min().unwrap();
                let mut tmp = Vec::new();
                for i in 0..len {
                    if cands.iter().map(|l| l[i]).all(|p| p == cands[0][i]) {
                        tmp.push(cands[0][i]);
                    } else {
                        break;
                    }
                }
                tmp
            }
        };
        memo.insert(start, path.clone());
        path
    }
}
