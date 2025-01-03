//! <https://adventofcode.com/2022/day/17>
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::Dim2,
        progress,
    },
    std::collections::{HashMap, HashSet, VecDeque},
};

type Loc = (usize, usize);

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Puzzle {
    line: Vec<isize>,
    shape: [Vec<Dim2<usize>>; 5],
    shape_h: [Vec<Dim2<usize>>; 5],
    shape_v: [Vec<Dim2<usize>>; 5],
}

#[aoc(2022, 17)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        if !block.is_empty() {
            self.line = block
                .trim()
                .chars()
                .map(|c| (c == '>') as usize as isize * 2 - 1)
                .collect::<Vec<isize>>();
        }
        Ok(())
    }
    fn end_of_data(&mut self) {
        self.shape = [
            vec![(0, 0), (1, 0), (2, 0), (3, 0)],
            vec![(1, 0), (0, 1), (1, 1), (2, 1), (1, 2)],
            vec![(0, 0), (1, 0), (2, 0), (2, 1), (2, 2)],
            vec![(0, 0), (0, 1), (0, 2), (0, 3)],
            vec![(0, 0), (1, 0), (0, 1), (1, 1)],
        ];
        self.shape_h = [
            vec![(0, 0), (3, 0)],
            vec![(1, 0), (0, 1), (2, 1), (1, 2)],
            vec![(0, 0), (2, 0), (2, 1), (2, 2)],
            vec![(0, 0), (0, 1), (0, 2), (0, 3)],
            vec![(0, 0), (1, 0), (0, 1), (1, 1)],
        ];
        self.shape_v = [
            vec![(0, 0), (1, 0), (2, 0), (3, 0)],
            vec![(1, 0), (0, 1), (2, 1)],
            vec![(0, 0), (1, 0), (2, 0)],
            vec![(0, 0)],
            vec![(0, 0), (1, 0)],
        ];
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut wind = self.line.iter().cycle();
        macro_rules! blow {
            ($x: expr, $w: expr) => {
                // ($x as isize + wind.next().unwrap()).clamp(1, 8 - $w) as usize
                {
                    let w = *wind.next().unwrap();
                    // println!("{}", if 0 < w { "right" } else { "left" });
                    ($x as isize + w).clamp(1, 8 - $w) as usize
                }
            };
        }
        let mut blocks: HashSet<Loc> = HashSet::new();
        for i in 0..7 {
            blocks.insert((i, 0));
        }
        let shape_w = [4, 3, 3, 1, 2];
        let mut bottom = 0;
        for i in 0..2022 {
            let id = i % 5;
            let mut x: usize = 3;
            x = blow!(x, shape_w[id]);
            x = blow!(x, shape_w[id]);
            x = blow!(x, shape_w[id]);
            let mut y = bottom + 1;
            loop {
                let tmp_x = blow!(x, shape_w[id]);
                if !clash((tmp_x, y), &self.shape_h[id], &blocks) {
                    x = tmp_x;
                }
                let tmp_y = y - 1;
                if clash((x, tmp_y), &self.shape_v[id], &blocks) {
                    break;
                }
                y = tmp_y;
            }
            bottom = place((x, y), &self.shape[id], &mut blocks, bottom);
        }
        bottom
    }
    fn part2(&mut self) -> Self::Output2 {
        let target = 1000000000000;
        let (header_len, _header_height, unit_len, unit_height) = self.cyclic_pattern(None);
        let num_units = (target - header_len) / unit_len;
        let remain_len = (target - header_len) % unit_len;
        let remain_height = self.cyclic_pattern(Some(header_len + remain_len)).0;
        num_units * unit_height + remain_height
    }
}

impl Puzzle {
    fn cyclic_pattern(&mut self, upto: Option<usize>) -> (usize, usize, usize, usize) {
        let depth = 34;
        const MEMORY_LEN: usize = 7;
        let mut memory: HashMap<[usize; MEMORY_LEN + 1], (usize, usize)> = HashMap::new();
        let mut cycles = 0;
        let mut pre_bottom = 0;
        let mut pre_x: VecDeque<usize> = VecDeque::new();
        let mut wind = self.line.iter().cycle();
        let wind_cycle = self.line.len();
        macro_rules! blow {
            ($x: expr, $w: expr) => {
                ($x as isize + wind.next().unwrap()).clamp(1, 8 - $w) as usize
            };
        }
        let mut blocks: HashSet<Loc> = HashSet::new();
        for i in 0..7 {
            blocks.insert((i, 0));
        }
        let shape_w = [4, 3, 3, 1, 2];
        let mut bottom = 0;
        for i in 0..upto.unwrap_or(usize::MAX) {
            let id = i % 5;
            if upto.is_none() && 0 < i && i % wind_cycle == 0 && id == 0 {
                cycles += 1;
                let key = [
                    bottom - pre_bottom,
                    pre_x[0],
                    pre_x[1],
                    pre_x[2],
                    pre_x[3],
                    pre_x[4],
                    pre_x[5],
                    pre_x[6],
                ];
                progress!(format!("cycle:{cycles:>4}, blocks:{i:>8}"));
                if let Some((header_len, header_height)) = memory.get(&key) {
                    progress!("");
                    return (
                        *header_len,
                        *header_height,
                        i - *header_len,
                        bottom - *header_height,
                    );
                }
                memory.insert(key, (i, bottom));
                pre_bottom = bottom;
            }
            let mut x: usize = 3;
            x = blow!(x, shape_w[id]);
            x = blow!(x, shape_w[id]);
            x = blow!(x, shape_w[id]);
            let mut y = bottom + 1;
            loop {
                let tmp_x = blow!(x, shape_w[id]);
                if !clash((tmp_x, y), &self.shape_h[id], &blocks) {
                    x = tmp_x;
                }
                let tmp_y = y - 1;
                if clash((x, tmp_y), &self.shape_v[id], &blocks) {
                    break;
                }
                y = tmp_y;
            }
            bottom = place((x, y), &self.shape[id], &mut blocks, bottom);
            pre_x.push_front(x);
            if i % 20 == 19 {
                blocks.retain(|(_, h)| bottom <= *h + depth);
                pre_x.resize(MEMORY_LEN, 0);
            }
        }
        (bottom, 0, 0, 0)
    }
}

fn clash(loc: Loc, shape: &[Loc], map: &HashSet<Loc>) -> bool {
    shape
        .iter()
        .any(|(x, y)| map.contains(&(x + loc.0, y + loc.1)))
}

fn place(loc: Loc, shape: &[Loc], map: &mut HashSet<Loc>, bottom: usize) -> usize {
    let mut b = bottom;
    for (x, y) in shape.iter() {
        map.insert((x + loc.0, y + loc.1));
        b = b.max(y + loc.1);
    }
    b
}

#[allow(dead_code)]
fn print(map: &HashSet<Loc>) {
    for y in (1..(2 + map.iter().map(|(_, y)| *y).max().unwrap_or_default())).rev() {
        print!("|");
        for x in 1..=7 {
            print!("{}", if map.contains(&(x, y)) { '#' } else { '.' });
        }
        println!("|");
    }
    println!("+-------+");
}
