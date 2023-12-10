//! <https://adventofcode.com/2023/day/10>
use {
    crate::{
        color,
        framework::{aoc, AdventOfCode, ParseError},
    },
    itertools::Itertools,
    std::collections::{HashMap, HashSet},
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
        dbg!(height, width);
        let mut insides: HashSet<(usize, usize)> = HashSet::new();
        let mut walls: HashSet<(usize, usize)> = HashSet::new();
        let loops = [(1, 0), (-1, 0), (0, -1), (0, 1)]
            .iter()
            .flat_map(|dir: &Pos2| {
                let mut pre: Pos2 = self.start;
                let mut pos = Some(add(&self.start, dir));
                let mut mapping: HashSet<((usize, usize), (usize, usize))> = HashSet::new();
                let mut route: HashMap<(usize, usize), char> = HashMap::new();
                // map.insert((self.start.0 as usize, self.start.1 as usize));
                while let Some(p) = pos {
                    if p.0 < 0 || height as isize <= p.0 || p.1 < 0 || width as isize <= p.1 {
                        return None;
                    }
                    assert_ne!(pre, p);
                    mapping.insert((
                        (pre.0 as usize, pre.1 as usize),
                        (p.0 as usize, p.1 as usize),
                    ));
                    let ch = match (p.0 - pre.0, p.1 - pre.1) {
                        (-1, 0) => '↑',
                        (1, 0) => '↓',
                        (0, -1) => '←',
                        (0, 1) => '→',
                        _ => unreachable!(),
                    };
                    route.insert((pre.0 as usize, pre.1 as usize), ch);
                    let next = self.line[p.0 as usize][p.1 as usize].go_through(&p, &pre);
                    pre = p;
                    pos = next;
                }
                Some((mapping, route))
            })
            .collect::<Vec<_>>();
        let longest = loops.iter().map(|m| m.1.len()).max().unwrap();
        let (map, route) = loops
            .iter()
            .filter(|m| m.0.len() == longest)
            .collect::<Vec<_>>()[0];
        let res = (0..height)
            .map(|y| {
                let mut span = 0;
                let mut inside = true;
                let xs = map
                    .iter()
                    .filter(|(p, _)| p.0 == y)
                    .map(|(p, _)| p.1)
                    .sorted()
                    .collect::<Vec<_>>();
                if xs.is_empty() {
                    return 0;
                }
                // if y == 3 {
                //     println!("{:?}", &xs);
                //     println!(
                //         "{:?}",
                //         map.iter()
                //             .filter(|(p, q)| p.0 == y && q.0 == y)
                //             .map(|(p, q)| (p.1, q.1))
                //             .sorted()
                //             .collect::<Vec<_>>()
                //     );
                // }
                // dbg!(y, &xs);
                let mut pre = xs[0];
                for x in xs.iter().skip(1) {
                    // if y == 3 {
                    //     println!(
                    //         "{} => {} :: check ({},{}) <-> ({},{})",
                    //         pre, x, y, pre, y, *x
                    //     );
                    // }
                    if inside {
                        // dbg!(x, pre);
                        span += *x - pre - 1;
                        for t in pre..*x {
                            insides.insert((y, t));
                        }
                    }
                    if !map.contains(&((y, *x), (y, *x + 1)))
                        && !map.contains(&((y, *x + 1), (y, *x)))
                    {
                        inside = !inside;
                        // if y == 3 {
                        //     println!("{} => {:?}", x, inside);
                        // }
                    }
                    pre = *x;
                }
                span
            })
            .sum();
        for y in 0..height {
            for x in 0..width {
                if let Some(ch) = route.get(&(y, x)) {
                    print!("{}{}{}", color::RED, ch, color::RESET);
                } else if insides.contains(&(y, x)) {
                    print!("{}⌾{}", color::GREEN, color::RESET);
                } else {
                    print!(" ");
                }
            }
            println!();
        }
        res
    }
}

// fn colorize(height: usize, width: usize, map: &HashSet<(usize, usize)>) -> (usize, usize, usize) {
//     // 0: outer
//     // 1: unknown => inner
//     // 2: border
//     let mut m = (0..height)
//         .map(|_| (0..width).map(|_| 1usize).collect::<Vec<_>>())
//         .collect::<Vec<_>>();
//     // assert!(map.iter().all(|(y, x)| *y * *x != 0));
//     let mut to_visit: Vec<(usize, usize)> = Vec::new();
//     for (y, l) in m.iter_mut().enumerate() {
//         for (x, p) in l.iter_mut().enumerate() {
//             if map.contains(&(y, x)) {
//                 *p = 2;
//             } else if y * x == 0 || y == height - 1 || x == width - 1 {
//                 *p = 0;
//                 to_visit.push((y, x));
//             }
//         }
//     }
//     for l in m.iter() {
//         for c in l.iter() {
//             print!("{c}");
//         }
//         println!();
//     }
//     while let Some(p) = to_visit.pop() {
//         m[p.0][p.1] = 0;
//         for l in geometric::neighbors8(p.0, p.1, height, width) {
//             if m[l.0][l.1] == 1 && !to_visit.contains(&l) {
//                 to_visit.push(l);
//             }
//         }
//     }
//     let mut ans = [0, 0, 0];
//     for l in m.iter() {
//         for p in l.iter() {
//             ans[*p] += 1;
//         }
//     }
//     for l in m.iter() {
//         for c in l.iter() {
//             print!("{c}");
//         }
//         println!();
//     }
//     (ans[0], ans[1], ans[2])
// }
