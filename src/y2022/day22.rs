//! <https://adventofcode.com/2022/day/22>
use {
    crate::{
        // color,
        framework::{aoc, AdventOfCode, ParseError},
        geometric::{Dim2, Vec2},
        parser::parse_usize,
    },
    std::collections::HashMap,
    winnow::{
        ascii::newline,
        combinator::{alt, repeat, separated, seq},
        token::one_of,
        PResult, Parser,
    },
};

type Loc = Dim2<usize>;
type Map = (HashMap<Loc, char>, HashMap<Loc, Loc>, HashMap<Loc, Loc>);

/// plane coord, direction
type AffineFrom = (Loc, Vec2);
/// new plane, position vector, new direction
type AffineTo = (Loc, Vec2, Vec2);

const FLIP_TABLE: [(AffineFrom, AffineTo); 14] = [
    (((0, 1), (-1, 0)), ((3, 0), (1, 0), (0, 1))),
    (((0, 1), (0, -1)), ((2, 0), (-1, 0), (0, 1))),
    (((0, 2), (-1, 0)), ((3, 0), (2, 1), (-1, 0))),
    (((0, 2), (0, 1)), ((2, 1), (-1, 2), (0, -1))),
    (((0, 2), (1, 0)), ((1, 1), (1, 2), (0, -1))),
    (((1, 1), (0, 1)), ((0, 2), (2, 1), (-1, 0))),
    (((1, 1), (0, -1)), ((2, 0), (0, 1), (1, 0))),
    (((2, 0), (0, -1)), ((0, 1), (-1, 0), (0, 1))),
    (((2, 0), (-1, 0)), ((1, 1), (1, 0), (0, 1))),
    (((2, 1), (0, 1)), ((0, 2), (-1, 2), (0, -1))),
    (((2, 1), (1, 0)), ((3, 0), (1, 2), (0, -1))),
    (((3, 0), (0, 1)), ((2, 1), (2, 1), (-1, 0))),
    (((3, 0), (1, 0)), ((0, 2), (0, 1), (1, 0))),
    (((3, 0), (0, -1)), ((0, 1), (0, 1), (1, 0))),
];

trait GeometricMove {
    fn position_to_move(&self, dir: &Vec2) -> Self;
}

impl GeometricMove for Loc {
    fn position_to_move(&self, dir: &Vec2) -> Self {
        (
            (self.0 as isize + dir.0) as usize,
            (self.1 as isize + dir.1) as usize,
        )
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Direction {
    Go(usize),
    TurnLeft,
    TurnRight,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct Seeker {
    position: Loc,
    direction: Vec2,
    trace: Vec<Loc>,
    plane_size: usize,
}

impl Default for Seeker {
    fn default() -> Self {
        Seeker {
            position: (0, 0),
            direction: (0, 1),
            trace: Vec::new(),
            plane_size: 1,
        }
    }
}

impl Seeker {
    fn to_password(&self) -> usize {
        (self.position.0 + 1) * 1000
            + (self.position.1 + 1) * 4
            + match self.direction {
                (0, 1) => 0,
                (1, 0) => 1,
                (0, -1) => 2,
                (-1, 0) => 3,
                _ => unreachable!(),
            }
    }
    fn position_in_plane(&self) -> usize {
        if self.horizontal() {
            self.position.0 % self.plane_size
        } else {
            self.position.1 % self.plane_size
        }
    }
    fn jump_parameters(&self) -> (Loc, Vec2) {
        (
            (
                self.position.0 / self.plane_size,
                self.position.1 / self.plane_size,
            ),
            self.direction,
        )
    }
    fn jump_to(&mut self, pos: &Loc) {
        self.position = *pos;
        self.trace.push(self.position);
    }
    fn direction(&mut self, dir: &Vec2) {
        self.direction = *dir;
    }
    fn go_forward(&mut self) {
        self.position = self.position.position_to_move(&self.direction);
        self.trace.push(self.position);
    }
    fn horizontal(&self) -> bool {
        self.direction.1 != 0
    }
    fn turn_right(&mut self) {
        self.direction = match self.direction {
            (0, 1) => (1, 0),
            (1, 0) => (0, -1),
            (0, -1) => (-1, 0),
            (-1, 0) => (0, 1),
            _ => unreachable!(),
        }
    }
    fn turn_left(&mut self) {
        self.direction = match self.direction {
            (0, 1) => (-1, 0),
            (1, 0) => (0, 1),
            (0, -1) => (1, 0),
            (-1, 0) => (0, -1),
            _ => unreachable!(),
        }
    }
    fn next_position(&self) -> Loc {
        self.position.position_to_move(&self.direction)
    }
    #[allow(clippy::collapsible_else_if)]
    fn step(
        &mut self,
        direction: &Direction,
        map: &Map,
        transform: Option<&HashMap<AffineFrom, AffineTo>>,
    ) {
        match direction {
            Direction::Go(steps) => {
                for _ in 0..*steps {
                    let next = self.next_position();
                    if let Some(land) = map.0.get(&next) {
                        match land {
                            '.' => self.go_forward(),
                            '#' => break,
                            _ => unreachable!(),
                        }
                    } else if let Some(affine) = transform {
                        let to = affine.get(&self.jump_parameters()).unwrap();
                        let offset = self.position_in_plane();
                        let new_position = (
                            to.0 .0 * self.plane_size
                                + match to.1 .0 {
                                    -1 => self.plane_size - offset - 1,
                                    0 => 0,
                                    1 => offset,
                                    2 => self.plane_size - 1,
                                    _ => unreachable!(),
                                },
                            to.0 .1 * self.plane_size
                                + match to.1 .1 {
                                    -1 => self.plane_size - offset - 1,
                                    0 => 0,
                                    1 => offset,
                                    2 => self.plane_size - 1,
                                    _ => unreachable!(),
                                },
                        );
                        match map.0.get(&new_position) {
                            Some(&'.') => {
                                // if self.trace.len() < 600 {
                                //     println!(
                                //         "jump from {:?} with offset {} to {:?}",
                                //         self.position, offset, new_position
                                //     );
                                // }
                                self.jump_to(&new_position);
                                self.direction(&to.2);
                            }
                            Some(&'#') => {
                                break;
                            }
                            _ => unreachable!(),
                        }
                    } else if let Some(pos) = if self.horizontal() {
                        map.1.get(&self.position)
                    } else {
                        map.2.get(&self.position)
                    } {
                        match map.0.get(pos) {
                            Some(&'.') => {
                                self.jump_to(pos);
                                // println!("jump to {:?}", self.position);
                            }
                            Some(&'#') => {
                                break;
                            }
                            _ => unreachable!(),
                        }
                    } else {
                        // for k in map
                        //     .1
                        //     .keys()
                        //     .filter(|(j, i)| *j == self.position.0 || *i == self.position.1)
                        // {
                        //     println!("jump table points {k:?}");
                        // }
                        panic!();
                    }
                    assert!(map.0.get(&self.position) == Some(&'.'));
                }
                assert!(map.0.get(&self.position) == Some(&'.'));
            }
            Direction::TurnLeft => {
                self.turn_left();
            }
            Direction::TurnRight => {
                self.turn_right();
            }
        }
        assert!(map.0.get(&self.position) == Some(&'.'));
        // println!("{:?}:{:?}", self.position, self.direction);
    }
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Puzzle {
    map: HashMap<Loc, char>,
    ring_h: HashMap<Loc, Loc>,
    ring_v: HashMap<Loc, Loc>,
    path: Vec<Direction>,
    line: Vec<Vec<char>>,
    plane_size: usize,
}

fn parse_maze_line(s: &mut &str) -> PResult<Vec<char>> {
    repeat(1.., one_of(&['.', '#', ' '])).parse_next(s)
}

fn parse_maze(s: &mut &str) -> PResult<Vec<Vec<char>>> {
    separated(1.., parse_maze_line, newline)
        .map(|v| dbg!(v))
        .parse_next(s)
}

fn parse_direction(s: &mut &str) -> PResult<Direction> {
    alt((
        parse_usize.map(Direction::Go),
        'R'.map(|_| Direction::TurnRight),
        'L'.map(|_| Direction::TurnLeft),
    ))
    .parse_next(s)
}

fn parse_directions(s: &mut &str) -> PResult<Vec<Direction>> {
    repeat(1.., parse_direction).map(|v| dbg!(v)).parse_next(s)
}

fn parse(s: &mut &str) -> PResult<(Vec<Vec<char>>, Vec<Direction>)> {
    seq!(parse_maze,  _: (newline, newline), parse_directions).parse_next(s)
}

#[aoc(2022, 22)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, input: String) -> Result<String, ParseError> {
        let (maze, moves) = parse(&mut input.as_str())?;
        self.line = maze;
        self.path = moves;
        Self::parsed()
    }
    fn end_of_data(&mut self) {
        for (j, l) in self.line.iter().enumerate() {
            for (i, c) in l.iter().enumerate() {
                if *c != ' ' {
                    self.map.insert((j, i), *c);
                }
            }
        }
        // build the edge map horizontally
        for (j, l) in self.line.iter().enumerate() {
            let width = l.len();
            let mut start = None;
            let mut end = None;
            for (i, _) in l.iter().enumerate() {
                if self.map.contains_key(&(j, i)) {
                    start = start.or(Some(i));
                } else if start.is_some() {
                    end = end.or(Some(i));
                }
                if end.is_some() {
                    break;
                }
            }
            end = end.or(Some(width));
            if let (Some(s), Some(e)) = (start, end) {
                self.ring_h.insert((j, s), (j, e - 1));
                self.ring_h.insert((j, e - 1), (j, s));
            } else {
                panic!();
            }
        }
        // build the edge map vertically
        let mut min_y: HashMap<usize, usize> = HashMap::new();
        let mut max_y: HashMap<usize, usize> = HashMap::new();
        let mut max_width = 0;
        for (j, l) in self.line.iter().enumerate() {
            for (i, _) in l.iter().enumerate() {
                max_width = max_width.max(i);
                if self.map.contains_key(&(j, i)) {
                    let e_min = min_y.entry(i).or_insert(usize::MAX);
                    *e_min = (*e_min).min(j);
                    let e_max = max_y.entry(i).or_insert(0);
                    *e_max = (*e_max).max(j);
                }
            }
        }
        for i in 0..=max_width {
            let start = min_y.get(&i);
            let end = max_y.get(&i);
            if let (Some(s), Some(e)) = (start, end) {
                self.ring_v.insert((*s, i), (*e, i));
                self.ring_v.insert((*e, i), (*s, i));
            } else {
                panic!();
            }
        }
        self.plane_size = (max_width + 1) / 3;
        debug_assert_eq!(
            self.plane_size, 50,
            "This problem is configured just for the real problem."
        );
    }
    fn dump(&self) {
        let affine = HashMap::from(FLIP_TABLE);
        let start = self.map.keys().min().unwrap();
        let mut seeker = Seeker {
            position: *start,
            plane_size: self.plane_size,
            ..Default::default()
        };
        let map = (self.map.clone(), self.ring_h.clone(), self.ring_v.clone());
        for d in self.path.iter() {
            seeker.step(d, &map, Some(&affine));
        }
        seeker.trace.resize(70, (0, 0));
        // let h = self.line.len();
        // let w = self.line.iter().map(|l| l.len()).max().unwrap_or_default();
        // for j in 0..h {
        //     for i in 0..w {
        //         if i == usize::MAX && self.map.contains_key(&(j, i)) {
        //             let p = (Seeker {
        //                 position: (j, i),
        //                 plane_size: self.plane_size,
        //                 ..Default::default()
        //             })
        //             .jump_parameters()
        //             .0;
        //             print!("{}", (b'A' + (p.0 * 3 + p.1) as u8) as char);
        //         }
        //     }
        //     // println!();
        // }
    }
    fn part1(&mut self) -> Self::Output1 {
        let start = self.map.keys().min().unwrap();
        let mut seeker = Seeker {
            position: *start,
            plane_size: self.plane_size,
            ..Default::default()
        };
        let map = (self.map.clone(), self.ring_h.clone(), self.ring_v.clone());
        for d in self.path.iter() {
            seeker.step(d, &map, None);
        }
        seeker.to_password()
    }
    fn part2(&mut self) -> Self::Output2 {
        let affine = HashMap::from(FLIP_TABLE);
        let start = self.map.keys().min().unwrap();
        let mut seeker = Seeker {
            position: *start,
            plane_size: self.plane_size,
            ..Default::default()
        };
        let map = (self.map.clone(), self.ring_h.clone(), self.ring_v.clone());
        for d in self.path.iter() {
            seeker.step(d, &map, Some(&affine));
        }
        seeker.to_password()
    }
}
