//! <https://adventofcode.com/2020/day/24>
use {
    crate::framework::{aoc, AdventOfCode, ParseError},
    std::collections::HashMap,
};

#[derive(Copy, Clone, Debug, PartialEq)]
pub enum Dir {
    E,
    SE,
    SW,
    W,
    NW,
    NE,
}

pub type Location = (isize, isize);

/// ```
/// use adventofcode::y2020::day24::*;
/// assert_eq!(location(&[Dir::E, Dir::SE, Dir::W]), (-1, 1));
/// assert_eq!(location(&[Dir::NW, Dir::W, Dir::SW, Dir::E, Dir::E]), (0, 0));
/// assert_eq!(location(&dirs_from("nwwswee")), (0, 0));
/// assert_eq!(location(&dirs_from("nwesw")), (0, 0));
/// ```
pub fn location(dirs: &[Dir]) -> Location {
    let up = dirs
        .iter()
        .filter(|d| [Dir::NW, Dir::NE].contains(d))
        .count() as isize;
    let down = dirs
        .iter()
        .filter(|d| [Dir::SW, Dir::SE].contains(d))
        .count() as isize;
    let right2 = dirs.iter().filter(|d| [Dir::E].contains(d)).count() as isize;
    let right = dirs
        .iter()
        .filter(|d| [Dir::SE, Dir::NE].contains(d))
        .count() as isize;
    let left2 = dirs.iter().filter(|d| [Dir::W].contains(d)).count() as isize;
    let left = dirs
        .iter()
        .filter(|d| [Dir::SW, Dir::NW].contains(d))
        .count() as isize;
    (up - down, (right2 - left2) * 2 + (right - left))
}

pub fn dirs_from(s: &str) -> Vec<Dir> {
    let mut vec: Vec<Dir> = Vec::new();
    push_dirs(&mut vec, s);
    vec
}

fn push_dirs(vec: &mut Vec<Dir>, s: &str) {
    if s.is_empty() {
        return;
    }
    for (prefix, symbol) in &[
        ("e", Dir::E),
        ("se", Dir::SE),
        ("sw", Dir::SW),
        ("w", Dir::W),
        ("nw", Dir::NW),
        ("ne", Dir::NE),
    ] {
        if let Some(remain) = s.strip_prefix(prefix) {
            vec.push(*symbol);
            return push_dirs(vec, remain);
        }
    }
    panic!("{}", s);
}

/// ```
/// use adventofcode::y2020::day24::*;
/// assert_eq!(neighbors(&(0,0)), [(0,2),(-1,1),(-1,-1),(0,-2),(1,-1),(1,1)]);
/// assert_eq!(neighbors(&(1,1)), [(1,3),(0,2),(0,0),(1,-1),(2,0),(2,2)]);
/// ```
pub fn neighbors((i, j): &Location) -> [Location; 6] {
    [
        (*i, *j + 2),
        (*i - 1, *j + 1),
        (*i - 1, *j - 1),
        (*i, *j - 2),
        (*i + 1, *j - 1),
        (*i + 1, *j + 1),
    ]
}

#[derive(Clone, Debug, Default, PartialEq)]
pub struct Puzzle {
    cell: HashMap<Location, bool>,
}

#[aoc(2020, 24)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.flip(location(&dirs_from(block)));
        Ok(())
    }
    // fn insert(&mut self, loc: Location) {
    //     self.flip(loc);
    // }
    fn part1(&mut self) -> usize {
        self.count()
    }
    fn part2(&mut self) -> usize {
        let n = 100;
        let mut w = self.clone();
        w.cell.retain(|_, v| *v);
        for _ in 1..=n {
            w = w.next_day();
            // println!("Day {}: {}", i, w.count());
        }
        w.count()
    }
}

impl Puzzle {
    fn flip(&mut self, loc: Location) {
        let entry = self.cell.entry(loc).or_insert(false);
        *entry = !*entry;
    }
    // fn set(&mut self, loc: Location, val: bool) {
    //     self.cell.insert(loc, val);
    // }
    fn get(&self, loc: &Location) -> bool {
        if let Some(b) = self.cell.get(loc) {
            *b
        } else {
            false
        }
    }
    fn count(&self) -> usize {
        self.cell.values().filter(|c| **c).count()
    }
    fn next_state(&self, loc: &Location) -> bool {
        let black_neighbors = neighbors(loc).iter().filter(|l| self.get(l)).count();
        if self.get(loc) {
            black_neighbors == 1 || black_neighbors == 2
        } else {
            black_neighbors == 2
        }
    }
    fn next_day(&self) -> Puzzle {
        let mut next: Puzzle = Puzzle::default();
        for (k, _v) in self.cell.iter() {
            /*
            if *v {
                println!("{:?}", k);
            }
            if self.next_state(k) {
                println!("\t\t=> {:?}", k);
            } */
            next.cell.insert(*k, self.next_state(k));
            for l in neighbors(k).iter() {
                if !next.cell.contains_key(l) {
                    next.cell.insert(*l, self.next_state(l));
                    /* if self.next_state(l) {
                        println!("\t\t=> {:?}", l);
                    } */
                }
            }
        }
        // shrink
        next.cell.retain(|_, v| *v);
        next
    }
}

#[cfg(feature = "y2020")]
#[cfg(test)]
mod test {
    use super::*;
    use crate::framework::*;
    const TEST1: &str = "\
sesenwnenenewseeswwswswwnenewsewsw
neeenesenwnwwswnenewnwwsewnenwseswesw
seswneswswsenwwnwse
nwnwneseeswswnenewneswwnewseswneseene
swweswneswnenwsewnwneneseenw
eesenwseswswnenwswnwnwsewwnwsene
sewnenenenesenwsewnenwwwse
wenwwweseeeweswwwnwwe
wsweesenenewnwwnwsenewsenwwsesesenwne
neeswseenwwswnwswswnw
nenwswwsewswnenenewsenwsenwnesesenew
enewnwewneswsewnwswenweswnenwsenwsw
sweneswneswneneenwnewenewwneswswnese
swwesenesewenwneswnwwneseswwne
enesenwswwswneneswsenwnewswseenwsese
wnwnesenesenenwwnenwsewesewsesesew
nenewswnwewswnenesenwnesewesw
eneswnwswnwsenenwnwnwwseeswneewsenese
neswnwewnwnwseenwseesewsenwsweewe
wseweeenwnesenwwwswnew";

    #[test]
    fn test1() {
        assert_eq!(
            Puzzle::solve(Description::TestData(TEST1.to_string()), 1),
            Answer::Part1(10)
        );
    }
    #[test]
    fn test2() {
        assert_eq!(
            Puzzle::solve(Description::TestData(TEST1.to_string()), 2),
            Answer::Part2(2208)
        );
    }
}
