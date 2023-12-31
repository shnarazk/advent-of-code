//! <https://adventofcode.com/2023/day/10>
use {
    crate::{
        // color,
        framework::{aoc, AdventOfCode, ParseError},
        geometric::{neighbors8, Dim2},
    },
    std::collections::{HashMap, HashSet},
};

const START: Dim2<isize> = (0, 0);

fn add((py, px): &Dim2<isize>, (qy, qx): &Dim2<isize>) -> Dim2<isize> {
    (py + qy, px + qx)
}

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Pipe(Vec<Dim2<isize>>);

impl Pipe {
    fn go_through(&self, at: &Dim2<isize>, from: &Dim2<isize>) -> Option<Dim2<isize>> {
        (self.0.len() == 2).then(|| add(&self.0[(*from == add(&self.0[0], at)) as usize], at))
    }
}
// fn goto()
#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Vec<Pipe>>,
    start: Dim2<isize>,
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
    fn serialize(&self) -> Option<String> {
        let mut hash: HashSet<Dim2<usize>> = HashSet::new();
        for (y, l) in self.line.iter().enumerate() {
            for (x, t) in l.iter().enumerate() {
                match t {
                    _ if *t == Pipe(vec![(-1, 0), (1, 0)]) => {
                        hash.insert((3 * y + 0, 3 * x + 1));
                        hash.insert((3 * y + 1, 3 * x + 1));
                        hash.insert((3 * y + 2, 3 * x + 1));
                    }
                    _ if *t == Pipe(vec![(0, -1), (0, 1)]) => {
                        hash.insert((3 * y + 1, 3 * x + 0));
                        hash.insert((3 * y + 1, 3 * x + 1));
                        hash.insert((3 * y + 1, 3 * x + 2));
                    }
                    _ if *t == Pipe(vec![(-1, 0), (0, 1)]) => {
                        hash.insert((3 * y + 0, 3 * x + 1));
                        hash.insert((3 * y + 1, 3 * x + 1));
                        hash.insert((3 * y + 1, 3 * x + 2));
                    }
                    _ if *t == Pipe(vec![(-1, 0), (0, -1)]) => {
                        hash.insert((3 * y + 0, 3 * x + 1));
                        hash.insert((3 * y + 1, 3 * x + 1));
                        hash.insert((3 * y + 1, 3 * x + 0));
                    }
                    _ if *t == Pipe(vec![(1, 0), (0, 1)]) => {
                        hash.insert((3 * y + 2, 3 * x + 1));
                        hash.insert((3 * y + 1, 3 * x + 1));
                        hash.insert((3 * y + 1, 3 * x + 2));
                    }
                    _ if *t == Pipe(vec![(1, 0), (0, -1)]) => {
                        hash.insert((3 * y + 2, 3 * x + 1));
                        hash.insert((3 * y + 1, 3 * x + 1));
                        hash.insert((3 * y + 1, 3 * x + 0));
                    }
                    _ => (),
                }
            }
        }
        let vec: Vec<Vec<_>> = (0..(3 * self.line.len()))
            .map(|y| {
                (0..(3 * self.line[0].len()))
                    .map(|x| hash.contains(&(y, x)))
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        serde_json::to_string(&vec).ok()
    }
    fn part1(&mut self) -> Self::Output1 {
        let height = self.line.len() as isize;
        let width = self.line[0].len() as isize;
        [(1, 0), (-1, 0), (0, -1), (0, 1)]
            .iter()
            .map(|dir: &Dim2<isize>| {
                let mut pre: Dim2<isize> = self.start;
                let mut pos = Some(add(&self.start, dir));
                let mut step = 1;
                while let Some(p) = pos {
                    if p.0 < 0 || height <= p.0 || p.1 < 0 || width <= p.1 {
                        break;
                    }
                    let next = self.line[p.0 as usize][p.1 as usize].go_through(&p, &pre);
                    pre = p;
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
            .flat_map(|dir: &Dim2<isize>| {
                let mut pre: Dim2<isize> = self.start;
                let mut pos = Some(add(&self.start, dir));
                let mut route: HashMap<(usize, usize), (isize, isize)> = HashMap::new();
                while let Some(p) = pos {
                    if p.0 < 0 || height as isize <= p.0 || p.1 < 0 || width as isize <= p.1 {
                        return None;
                    }
                    route.insert((pre.0 as usize, pre.1 as usize), (p.0 - pre.0, p.1 - pre.1));
                    let next = self.line[p.0 as usize][p.1 as usize].go_through(&p, &pre);
                    pre = p;
                    pos = next;
                }
                Some(route)
            })
            .collect::<Vec<_>>();
        let longest = loops.iter().map(|r| r.len()).max().unwrap();
        let route = loops
            .iter()
            .filter(|r| r.len() == longest)
            .collect::<Vec<_>>()[0];
        colorize(height, width, route).1
    }
}

// By scaling up, we can shed hidden corrridors
fn colorize(
    height: usize,
    width: usize,
    map: &HashMap<(usize, usize), (isize, isize)>,
) -> (usize, usize, usize) {
    // 0: outer
    // 1: unknown => inner
    // 2: border
    let h2 = 2 * height;
    let w2 = 2 * width;
    let mut m = (0..h2)
        .map(|_| (0..w2).map(|_| 1usize).collect::<Vec<_>>())
        .collect::<Vec<_>>();
    let mut to_visit: Vec<(usize, usize)> = Vec::new();
    for y in 0..height {
        for x in 0..width {
            if let Some(dir) = map.get(&(y, x)) {
                m[2 * y][2 * x] = 2;
                m[(2 * y as isize + dir.0) as usize][(2 * x as isize + dir.1) as usize] = 2;
            }
        }
    }
    for (y, l) in m.iter_mut().enumerate() {
        for (x, p) in l.iter_mut().enumerate() {
            if *p != 2 && y * x == 0 || y == h2 - 1 || x == w2 - 1 {
                *p = 0;
                to_visit.push((y, x));
            }
        }
    }
    while let Some(p) = to_visit.pop() {
        m[p.0][p.1] = 0;
        for l in neighbors8(p.0, p.1, h2, w2) {
            if m[l.0][l.1] == 1 && !to_visit.contains(&l) {
                to_visit.push(l);
            }
        }
    }
    // for y in 0..height {
    //     for x in 0..width {
    //         match m[2 * y][2 * x] {
    //             0 => print!("_"),
    //             1 => print!("{}⌾{}", color::GREEN, color::RESET),
    //             2 => print!("{}#{}", color::RED, color::RESET),
    //             _ => unreachable!(),
    //         }
    //     }
    //     println!();
    // }
    let mut ans = [0, 0, 0];
    for y in 0..height {
        for x in 0..width {
            ans[m[2 * y][2 * x]] += 1;
        }
    }
    (ans[0], ans[1], ans[2])
}
