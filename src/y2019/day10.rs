//! <https://adventofcode.com/2019/day/10>
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        math::gcd,
    },
    std::collections::{HashMap, HashSet, VecDeque},
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Vec<bool>>,
}

#[aoc(2019, 10)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.line
            .push(block.chars().map(|c| c == '#').collect::<Vec<bool>>());
        Ok(())
    }
    fn after_insert(&mut self) {
        let height = self.line.len();
        let width = self.line[0].len();
        dbg!(height, width);
    }
    fn part1(&mut self) -> Self::Output1 {
        let _height = self.line.len();
        let _width = self.line[0].len();
        let mut best = (0, 0);
        let mut max_visible = 0;
        for (j, l) in self.line.iter().enumerate() {
            for (i, p) in l.iter().enumerate() {
                if !p {
                    continue;
                }
                let mut visible: HashSet<(isize, isize)> = HashSet::new();
                for (jj, ll) in self.line.iter().enumerate() {
                    for (ii, pp) in ll.iter().enumerate() {
                        if *pp {
                            let dy = jj as isize - j as isize;
                            let dx = ii as isize - i as isize;
                            match (dy, dx) {
                                (0, 0) => (),
                                (0, _) => {
                                    visible.insert((0, dx.signum()));
                                }
                                (_, 0) => {
                                    visible.insert((dy.signum(), 0));
                                }
                                _ => {
                                    let factor = gcd(dy.unsigned_abs(), dx.unsigned_abs()) as isize;
                                    visible.insert((dy / factor, dx / factor));
                                }
                            }
                        }
                    }
                }
                let n = visible.len();
                if max_visible < n {
                    max_visible = n;
                    best = (j, i);
                }
            }
        }
        dbg!(&best);
        max_visible
    }
    fn part2(&mut self) -> Self::Output2 {
        for p in [
            (-1, 0),
            (-4, 2),
            (-4, 5),
            (0, 1),
            (1, 4),
            (1, 2),
            (1, 0),
            (1, -2),
            (1, -3),
            (0, -1),
            (-1, -5),
            (-1, -2),
            (-2, -1),
        ] {
            println!("mk_rad({}, {}) = {}", p.0, p.1, mk_rad(p.0, p.1));
        }
        type Loc = (usize, usize, usize);
        type Degree = (isize, isize);
        let oy = 29;
        let ox = 23;
        let mut visible: HashMap<Degree, Vec<Loc>> = HashMap::new();
        for (jj, ll) in self.line.iter().enumerate() {
            for (ii, pp) in ll.iter().enumerate() {
                if *pp {
                    let dy = jj as isize - oy as isize;
                    let dx = ii as isize - ox as isize;
                    match (dy, dx) {
                        (0, 0) => (),
                        (0, _) => {
                            let entry = visible.entry((0, dx.signum())).or_insert(Vec::new());
                            entry.push((dx.unsigned_abs(), jj, ii));
                        }
                        (_, 0) => {
                            let entry = visible.entry((dy.signum(), 0)).or_insert(Vec::new());
                            entry.push((dy.unsigned_abs(), jj, ii));
                        }
                        _ => {
                            let factor = gcd(dy.unsigned_abs(), dx.unsigned_abs()) as isize;
                            let entry = visible
                                .entry((dy / factor, dx / factor))
                                .or_insert(Vec::new());
                            entry.push((factor as usize, jj, ii));
                        }
                    }
                }
            }
        }
        let mut list: Vec<(f64, VecDeque<Loc>)> = visible
            .iter()
            .map(|(k, l)| {
                let mut lst = l.clone();
                lst.sort();
                (mk_rad(k.0, k.1), VecDeque::from(lst))
            })
            .collect::<Vec<_>>();
        list.sort_by(|a, b| a.0.total_cmp(&b.0));
        let mut queue: VecDeque<VecDeque<Loc>> =
            list.into_iter().map(|(_, l)| l).collect::<VecDeque<_>>();
        let mut count = 0;
        let mut result = 0;
        while count < 200 {
            if let Some(mut q) = queue.pop_front() {
                if !q.is_empty() {
                    count += 1;
                    if let Some(vaporized) = q.pop_front() {
                        result = vaporized.1 + vaporized.2 * 100;
                        // println!("{:?}", vaporized);
                    }
                    queue.push_back(q);
                }
            }
        }
        result
    }
}

fn mk_rad(y: isize, x: isize) -> f64 {
    let ay = y.abs() as f64;
    let ax = x.abs() as f64;
    match (y.signum(), x.signum()) {
        (-1, 0) => 0.0,
        (-1, 1) => std::f64::consts::FRAC_PI_2 - (ay / ax).atan(),
        (0, 1) => std::f64::consts::FRAC_PI_2,
        (1, 1) => std::f64::consts::FRAC_PI_2 + (ay / ax).atan(),
        (1, 0) => std::f64::consts::PI,
        (1, -1) => 3.0 * std::f64::consts::FRAC_PI_2 - (ay / ax).atan(),
        (0, -1) => 3.0 * std::f64::consts::FRAC_PI_2,
        (-1, -1) => 3.0 * std::f64::consts::FRAC_PI_2 + (ay / ax).atan(),
        _ => unreachable!(),
    }
}
