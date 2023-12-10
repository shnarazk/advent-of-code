//! <https://adventofcode.com/2023/day/10>
use {
    crate::framework::{aoc, AdventOfCode, ParseError},
    std::collections::HashSet,
};

type Pos2 = (isize, isize);
const START: Pos2 = (0, 0);

fn add((py, px): &Pos2, (qy, qx): &Pos2) -> Pos2 {
    (py + qy, px + qx)
}

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Pipe(Vec<Pos2>);

impl Pipe {
    fn go_through(&self, at: &Pos2, from: &Pos2) -> Option<Pos2> {
        (self.0.len() == 2).then(|| add(&self.0[(*from == add(&self.0[0], at)) as usize], at))
    }
}
// fn goto()
#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Vec<Pipe>>,
    start: Pos2,
}

#[aoc(2023, 10)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        let l = block
            .trim()
            .chars()
            .map(|c| match c {
                '|' => Pipe(vec![(-1, 0), (1, 0)]),
                '-' => Pipe(vec![(0, -1), (0, 1)]),
                'L' => Pipe(vec![(-1, 0), (0, 1)]),
                'J' => Pipe(vec![(-1, 0), (0, -1)]),
                '7' => Pipe(vec![(1, 0), (0, -1)]),
                'F' => Pipe(vec![(1, 0), (0, 1)]),
                '.' => Pipe(vec![]),
                'S' => Pipe(vec![START]),
                _ => unreachable!(),
            })
            .collect::<Vec<Pipe>>();
        self.line.push(l);
        Ok(())
    }
    fn end_of_data(&mut self) {
        for (y, l) in self.line.iter().enumerate() {
            for (x, p) in l.iter().enumerate() {
                if p.0 == vec![START] {
                    self.start = (y as isize, x as isize);
                    break;
                }
            }
        }
    }
    fn part1(&mut self) -> Self::Output1 {
        let height = self.line.len() as isize;
        let width = self.line[0].len() as isize;
        [(1, 0), (-1, 0), (0, -1), (0, 1)]
            .iter()
            .map(|dir: &Pos2| {
                let mut pre: Pos2 = self.start;
                let mut pos = Some(add(&self.start, dir));
                let mut step = 1;
                while let Some(p) = pos {
                    if p.0 < 0 || height <= p.0 || p.1 < 0 || width <= p.1 {
                        break;
                    }
                    // dbg!(p);
                    let next = self.line[p.0 as usize][p.1 as usize].go_through(&p, &pre);
                    pre = p;
                    // dbg!(next);
                    pos = next;
                    step += 1;
                }
                step / 2
            })
            .max()
            .unwrap()
    }
    fn part2(&mut self) -> Self::Output2 {
        let height = self.line.len();
        let width = self.line[0].len();
        let loops = [(1, 0), (-1, 0), (0, -1), (0, 1)]
            .iter()
            .flat_map(|dir: &Pos2| {
                let mut pre: Pos2 = self.start;
                let mut pos = Some(add(&self.start, dir));
                let mut map: HashSet<(usize, usize)> = HashSet::new();
                map.insert((self.start.0 as usize, self.start.1 as usize));
                while let Some(p) = pos {
                    if p.0 < 0 || height as isize <= p.0 || p.1 < 0 || width as isize <= p.1 {
                        return None;
                    }
                    map.insert((p.0 as usize, p.1 as usize));
                    let next = self.line[p.0 as usize][p.1 as usize].go_through(&p, &pre);
                    pre = p;
                    pos = next;
                }
                Some(map)
            })
            .collect::<Vec<_>>();
        let longest = loops.iter().map(|m| m.len()).max().unwrap();
        let l = loops
            .iter()
            .filter(|m| m.len() == longest)
            .collect::<Vec<_>>()[0];
        dbg!(l.iter().filter(|(y, x)| *y * *x == 0).count());
        let x = color(height, width, l);
        x.2
    }
}

fn color(height: usize, width: usize, map: &HashSet<(usize, usize)>) -> (usize, usize, usize) {
    let mut m = (0..height)
        .map(|_| (0..width).map(|_| 0).collect::<Vec<_>>())
        .collect::<Vec<_>>();
    assert!(map.iter().all(|(y, x)| *y * *x != 0));
    let mut to_check: Vec<(usize, usize)> = Vec::new();
    for (y, l) in m.iter_mut().enumerate() {
        for (x, p) in l.iter_mut().enumerate() {
            if map.contains(&(y, x)) {
                *p = 1;
            } else if y * x == 0 {
                *p = 2;
                to_check.push((y, x));
            }
        }
    }
    while let Some(p) = to_check.pop() {
        if m[p.0][p.1] != 0 {
            continue;
        }
    }
    (0, 0, 0)
}
