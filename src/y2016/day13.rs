//! <https://adventofcode.com/2016/day/13>
use {
    crate::{
        framework::{AdventOfCode, ParseError, aoc},
        geometric,
    },
    std::{
        cmp::Reverse,
        collections::{BinaryHeap, HashMap, HashSet},
    },
};

type Dim2 = (usize, usize);

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: usize,
}

#[aoc(2016, 13)]
impl AdventOfCode for Puzzle {
    fn prepare(&mut self, _: &str) -> Result<(), ParseError> {
        self.line = 1364;
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut map: HashMap<Dim2, bool> = HashMap::new();
        let start = (1, 1);
        let goal = (31, 39);
        let mut to_visit: BinaryHeap<Reverse<(usize, Dim2)>> = BinaryHeap::new();
        let mut visited: HashSet<Dim2> = HashSet::new();
        to_visit.push(Reverse((0, start)));
        while let Some(Reverse((dist, pos))) = to_visit.pop() {
            if pos == goal {
                return dist;
            }
            visited.insert(pos);
            for p in geometric::neighbors4(pos.0, pos.1, usize::MAX, usize::MAX) {
                if !visited.contains(&p) && get(&mut map, p.0, p.1, self.line) {
                    to_visit.push(Reverse((dist + 1, p)));
                }
            }
        }
        unreachable!()
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut map: HashMap<Dim2, bool> = HashMap::new();
        let start: Dim2 = (1, 1);
        let limit: usize = 50;
        let mut to_visit: BinaryHeap<Reverse<(usize, Dim2)>> = BinaryHeap::new();
        let mut visited: HashSet<Dim2> = HashSet::new();
        to_visit.push(Reverse((0, start)));
        while let Some(Reverse((dist, pos))) = to_visit.pop() {
            visited.insert(pos);
            if dist == limit {
                continue;
            }
            for p in geometric::neighbors4(pos.0, pos.1, usize::MAX, usize::MAX) {
                if !visited.contains(&p) && get(&mut map, p.0, p.1, self.line) {
                    to_visit.push(Reverse((dist + 1, p)));
                }
            }
        }
        visited.len()
    }
}

fn get(map: &mut HashMap<Dim2, bool>, x: usize, y: usize, key: usize) -> bool {
    if let Some(b) = map.get(&(x, y)) {
        return *b;
    }
    let b = {
        let sum = x * x + 3 * x + 2 * x * y + y + y * y + key;
        sum.count_ones().is_multiple_of(2)
    };
    map.insert((x, y), b);
    b
}
