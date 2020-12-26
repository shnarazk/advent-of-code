#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    lazy_static::lazy_static,
    regex::Regex,
    std::{
        collections::HashMap,
        io::{stdin, Read},
    },
};

pub fn day24(part: usize, buffer: String) {
    if part == 1 {
        dbg!(read(&buffer));
    } else {
        dbg!(read2(&buffer, 100));
    }
}

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
/// use adventofcode::main::*;
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
/// use adventofcode::main::*;
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

struct World {
    cell: HashMap<Location, bool>,
}

impl World {
    fn new() -> World {
        World {
            cell: HashMap::new(),
        }
    }
    fn flip(&mut self, loc: Location) {
        let entry = self.cell.entry(loc).or_insert(false);
        *entry = !*entry;
    }
    fn set(&mut self, loc: Location, val: bool) {
        self.cell.insert(loc, val);
    }
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
    fn next_day(&self) -> World {
        let mut next: World = World::new();
        for (k, v) in self.cell.iter() {
            if *v {
                println!("{:?}", k);
            }
            if self.next_state(k) {
                println!("\t\t=> {:?}", k);
            }
            next.cell.insert(*k, self.next_state(k));
            for l in neighbors(k).iter() {
                if next.cell.get(l).is_none() {
                    next.cell.insert(*l, self.next_state(l));
                    if self.next_state(l) {
                        println!("\t\t=> {:?}", l);
                    }
                }
            }
        }
        // shrink
        next.cell.retain(|_, v| *v);
        next
    }
}

fn read(buf: &str) -> usize {
    let mut dic: World = World::new();
    for l in buf.split('\n') {
        if l.is_empty() {
            break;
        }
        let dirs = dirs_from(l);
        dic.flip(location(&dirs));
    }
    // dbg!(dic.iter().filter(|(k, c)| 1 < **c).collect::<Vec<_>>());
    dic.count()
}

fn read2(buf: &str, n: usize) -> usize {
    let mut w: World = World::new();
    for l in buf.split('\n') {
        if l.is_empty() {
            break;
        }
        let dirs = dirs_from(l);
        w.flip(location(&dirs));
    }
    w.cell.retain(|_, v| *v);
    for i in 1..=n {
        w = w.next_day();
        println!("Day {}: {}", i, w.count());
    }
    w.count()
}

mod test {
    use super::*;
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
        assert_eq!(read(TEST1), 10);
    }
    #[test]
    fn test2() {
        assert_eq!(read2(TEST1, 1), 15);
    }
}
