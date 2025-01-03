//! <https://adventofcode.com/2021/day/19>
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        parser,
    },
    std::collections::HashMap,
};

type Pos = [isize; 3];

const UNIT: [Pos; 3] = [[1, 0, 0], [0, 1, 0], [0, 0, 1]];

const ROTATIONS: [[Pos; 3]; 24] = [
    [[1, 0, 0], [0, 1, 0], [0, 0, 1]],
    [[0, 0, 1], [0, 1, 0], [-1, 0, 0]],
    [[-1, 0, 0], [0, 1, 0], [0, 0, -1]],
    [[0, 0, -1], [0, 1, 0], [1, 0, 0]],
    [[0, -1, 0], [1, 0, 0], [0, 0, 1]],
    [[0, 0, 1], [1, 0, 0], [0, 1, 0]],
    [[0, 1, 0], [1, 0, 0], [0, 0, -1]],
    [[0, 0, -1], [1, 0, 0], [0, -1, 0]],
    [[0, 1, 0], [-1, 0, 0], [0, 0, 1]],
    [[0, 0, 1], [-1, 0, 0], [0, -1, 0]],
    [[0, -1, 0], [-1, 0, 0], [0, 0, -1]],
    [[0, 0, -1], [-1, 0, 0], [0, 1, 0]],
    [[1, 0, 0], [0, 0, -1], [0, 1, 0]],
    [[0, 1, 0], [0, 0, -1], [-1, 0, 0]],
    [[-1, 0, 0], [0, 0, -1], [0, -1, 0]],
    [[0, -1, 0], [0, 0, -1], [1, 0, 0]],
    [[1, 0, 0], [0, -1, 0], [0, 0, -1]],
    [[0, 0, -1], [0, -1, 0], [-1, 0, 0]],
    [[-1, 0, 0], [0, -1, 0], [0, 0, 1]],
    [[0, 0, 1], [0, -1, 0], [1, 0, 0]],
    [[1, 0, 0], [0, 0, 1], [0, -1, 0]],
    [[0, -1, 0], [0, 0, 1], [-1, 0, 0]],
    [[-1, 0, 0], [0, 0, 1], [0, 1, 0]],
    [[0, 1, 0], [0, 0, 1], [1, 0, 0]],
];

#[derive(Clone, Debug, Default)]
struct Block {
    id: usize,
    pos: Vec<Pos>,
}

#[allow(dead_code)]
fn matrix_product(m1: &[Pos; 3], m2: &[Pos; 3]) -> [Pos; 3] {
    [
        [
            m1[0][0] * m2[0][0] + m1[0][1] * m2[0][1] + m1[0][2] * m2[0][2],
            m1[0][0] * m2[1][0] + m1[0][1] * m2[1][1] + m1[0][2] * m2[1][2],
            m1[0][0] * m2[2][0] + m1[0][1] * m2[2][1] + m1[0][2] * m2[2][2],
        ],
        [
            m1[1][0] * m2[0][0] + m1[1][1] * m2[0][1] + m1[1][2] * m2[0][2],
            m1[1][0] * m2[1][0] + m1[1][1] * m2[1][1] + m1[1][2] * m2[1][2],
            m1[1][0] * m2[2][0] + m1[1][1] * m2[2][1] + m1[1][2] * m2[2][2],
        ],
        [
            m1[2][0] * m2[0][0] + m1[2][1] * m2[0][1] + m1[2][2] * m2[0][2],
            m1[2][0] * m2[1][0] + m1[2][1] * m2[1][1] + m1[2][2] * m2[1][2],
            m1[2][0] * m2[2][0] + m1[2][1] * m2[2][1] + m1[2][2] * m2[2][2],
        ],
    ]
}

fn matrix_dot(m: &[Pos; 3], v: &Pos) -> Pos {
    [
        m[0][0] * v[0] + m[0][1] * v[1] + m[0][2] * v[2],
        m[1][0] * v[0] + m[1][1] * v[1] + m[1][2] * v[2],
        m[2][0] * v[0] + m[2][1] * v[1] + m[2][2] * v[2],
    ]
}

impl Block {
    fn rotated(&self, axis: usize) -> Self {
        Block {
            id: 0,
            pos: self
                .pos
                .iter()
                .map(|p| matrix_dot(&ROTATIONS[axis], p))
                .collect::<Vec<_>>(),
        }
    }
}

#[derive(Clone, Debug, Default)]
pub struct Puzzle {
    line: Vec<Block>,
}

fn merge(mut sensors: Vec<Block>) -> (Vec<Pos>, Vec<Pos>) {
    // println!("merge {} sensors", sensors.len());
    let mut base: Vec<Pos> = sensors.remove(0).pos;
    let mut sensor_locations: Vec<Pos> = vec![[0, 0, 0]];
    let mut remove: Option<usize> = None;
    'matched: while !sensors.is_empty() {
        if let Some(i) = remove {
            sensors.retain(|s| s.id != i);
            // println!("remove sensor{:>2}, {} remains.", i, sensors.len());
            remove = None;
        }
        for sensor in sensors.iter() {
            let mut nsolutions = 0;
            // let mut good_rotation = 0;
            let mut good_estimation: Block = Block::default();
            let mut dx: isize = 0;
            let mut dy: isize = 0;
            let mut dz: isize = 0;
            let mut matches: usize = 12;
            for r_index in 0..ROTATIONS.len() {
                if 35 == r_index {
                    continue;
                }
                let mut x_dists: HashMap<isize, usize> = HashMap::new();
                let mut y_dists: HashMap<isize, usize> = HashMap::new();
                let mut z_dists: HashMap<isize, usize> = HashMap::new();
                let becons = sensor.rotated(r_index);
                for p0 in base.iter() {
                    for p1 in becons.pos.iter() {
                        *x_dists.entry(p0[0] - p1[0]).or_insert(0) += 1;
                        *y_dists.entry(p0[1] - p1[1]).or_insert(0) += 1;
                        *z_dists.entry(p0[2] - p1[2]).or_insert(0) += 1;
                    }
                }
                let axd = x_dists.iter().max_by_key(|(_, n)| *n).unwrap();
                let ayd = y_dists.iter().max_by_key(|(_, n)| *n).unwrap();
                let azd = z_dists.iter().max_by_key(|(_, n)| *n).unwrap();
                if matches <= *axd.1 && matches <= *ayd.1 && matches <= *azd.1 {
                    // println!(
                    //     " - sensor{:0>2} - r{}/{:?},{:?},{:?}",
                    //     sensor.id, r_index, axd, ayd, azd
                    // );
                    // good_rotation = r_index;
                    nsolutions += 1;
                    dx = *axd.0;
                    dy = *ayd.0;
                    dz = *azd.0;
                    matches = *axd.1.min(ayd.1).min(azd.1);
                    good_estimation = becons;
                }
            }
            if 0 < nsolutions {
                // assert_eq!(1, nsolutions);
                // println!(
                //     "sensor{:0>2} - r{}/{:?},{:?},{:?}",
                //     sensor.id, good_rotation, dx, dy, dz
                // );
                for p in good_estimation.pos.iter() {
                    let v = [p[0] + dx, p[1] + dy, p[2] + dz];
                    if !base.contains(&v) {
                        base.push(v);
                    } else {
                        // println!("{:?}", v);
                    }
                }
                sensor_locations.push([dx, dy, dz]);
                remove = Some(sensor.id);
                continue 'matched;
            }
        }
        if !sensors.is_empty() {
            // println!("check isolated group");
            sensors.push(Block {
                id: 0,
                pos: base.clone(),
            });
            base = sensors.remove(0).pos;
            // panic!("nothing happended; remains {}", sensors.len());
        }
    }
    debug_assert!(sensors.is_empty());
    (base, sensor_locations)
}

impl Puzzle {
    #[allow(dead_code)]
    fn build(&self) {
        const ROTATE: [[Pos; 3]; 6] = [
            [[0, -1, 0], [1, 0, 0], [0, 0, 1]], // z
            [[0, 1, 0], [-1, 0, 0], [0, 0, 1]], // -z
            [[0, 0, 1], [0, 1, 0], [-1, 0, 0]], // y
            [[0, 0, -1], [0, 1, 0], [1, 0, 0]], // -y
            [[1, 0, 0], [0, 0, 1], [0, -1, 0]], // x
            [[1, 0, 0], [0, 0, -1], [0, 1, 0]], // -x
        ];
        let mut bag: Vec<[Pos; 3]> = vec![UNIT];
        let mut old_len = 0;
        while old_len < bag.len() {
            old_len = bag.len();
            let mut newm = Vec::new();
            for m in bag.iter() {
                for r in ROTATE.iter() {
                    let n = matrix_product(r, m);
                    newm.push(n);
                    assert!(ROTATIONS.contains(&n), "{:?} <= {:?} {:?}", n, r, m,);
                }
            }
            for m in newm.iter() {
                if !bag.contains(m) {
                    bag.push(*m);
                }
            }
            println!("{}", bag.len());
        }
        bag.sort_unstable();
        println!("    [");
        for (i, m) in bag.iter().enumerate() {
            print!("        [ ");
            for v in m.iter() {
                print!(
                    "[{}], ",
                    v.iter()
                        .map(|n| format!("{:>2}", n))
                        .collect::<Vec<_>>()
                        .join(","),
                );
            }
            println!(" ], // {:2>}", i);
        }
        println!("];");
        panic!();
    }
}

#[aoc(2021, 19)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        let mut v = Vec::new();
        for line in block.split('\n').skip(1) {
            if line.is_empty() {
                continue;
            }
            let r = parser::to_isizes(line, &[','])?;
            if r.len() == 2 {
                v.push([r[0], r[1], 0]);
            } else {
                v.push([r[0], r[1], r[2]]);
            }
        }
        let n = self.line.len();
        self.line.push(Block { id: n, pos: v });
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        merge(self.line.clone()).0.len()
    }
    fn part2(&mut self) -> Self::Output2 {
        let dists = merge(self.line.clone()).1;
        let n = self.line.len();
        debug_assert_eq!(n, dists.len());
        (0..n)
            .map(|i| {
                (0..n)
                    .map(|j| {
                        (dists[j][0] - dists[i][0]).unsigned_abs()
                            + (dists[j][1] - dists[i][1]).unsigned_abs()
                            + (dists[j][2] - dists[i][2]).unsigned_abs()
                    })
                    .max()
                    .unwrap()
            })
            .max()
            .unwrap()
    }
}
