//! <https://adventofcode.com/2025/day/12>
use {
    crate::{
        array::{rotate_ccw, rotate_clockwise},
        framework::{AdventOfCode, ParseError, aoc},
        geometric::Dim2,
    },
    rayon::prelude::*,
    std::collections::BinaryHeap,
};

type Shape = (usize, usize, Vec<Vec<bool>>, Vec<Vec<Vec<bool>>>);
type Region = (usize, usize, Vec<usize>);

#[derive(Clone, Debug, Default)]
pub struct Puzzle {
    shapes: Vec<Shape>,
    regions: Vec<Region>,
}

mod parser {
    use {
        super::{Region, Shape},
        crate::parser::parse_usize,
        winnow::{
            ModalResult, Parser,
            ascii::{newline, space1},
            combinator::{repeat, separated, seq},
            token::one_of,
        },
    };

    fn parse_shape(s: &mut &str) -> ModalResult<Shape> {
        seq!(parse_usize, _: ":\n",
        separated(1.., repeat(1.., one_of(['.', '#']).map(|c: char| c == '#')).map(|v: Vec<bool>| v), newline),
            _: newline
        )
            .map(|(i, s):  (usize,Vec<Vec<bool>>)| {
let n = s.iter().map(|l| l.iter().filter(|b| **b).count()).sum();
                (i, n, s, vec![])})
        .parse_next(s)
    }
    fn parse_shapes(s: &mut &str) -> ModalResult<Vec<Shape>> {
        separated(1.., parse_shape, newline).parse_next(s)
    }
    fn parse_region(s: &mut &str) -> ModalResult<Region> {
        seq!(parse_usize, _ : "x", parse_usize, _: ": ", separated(1.., parse_usize, space1))
            .parse_next(s)
    }
    fn parse_regions(s: &mut &str) -> ModalResult<Vec<Region>> {
        separated(1.., parse_region, newline).parse_next(s)
    }
    pub fn parse(s: &mut &str) -> ModalResult<(Vec<Shape>, Vec<Region>)> {
        seq!(parse_shapes, _: newline, parse_regions).parse_next(s)
    }
}

#[derive(Clone, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
struct State {
    num_placed: usize,
    remain_rooms: usize,
    placed: Vec<usize>,
    grid: Vec<Vec<bool>>,
}

impl State {
    fn fill_by_grid_and_placed(mut self) -> Self {
        let height = self.grid.len();
        let width = self.grid[0].len();
        let mut h = 0;
        let mut w = 0;
        for (i, l) in self.grid.iter().enumerate() {
            for (j, b) in l.iter().enumerate() {
                if *b {
                    h = h.max(i);
                    w = w.max(j);
                }
            }
        }
        self.remain_rooms = height * width - h * w;
        self.num_placed = self.placed.iter().sum();
        self
    }
}

#[aoc(2025, 12)]
impl AdventOfCode for Puzzle {
    fn prepare(&mut self, mut input: &str) -> Result<(), ParseError> {
        let (s, r) = parser::parse(&mut input)?;
        self.shapes = s
            .into_iter()
            .map(|(id, count, shape, _)| {
                let variants = possible_directions(&shape);
                (id, count, shape, variants)
            })
            .collect::<Vec<_>>();
        self.regions = r;
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        self.regions
            .par_iter()
            .filter(|(width, height, required)| {
                // check a simple prop.
                if self
                    .shapes
                    .iter()
                    .enumerate()
                    .map(|(si, s)| s.1 * required[si])
                    .sum::<usize>()
                    > *height * *width
                {
                    return false;
                }
                let grid = vec![vec![false; *width]; *height];
                let placed = vec![0_usize; required.len()];
                let mut to_visit: BinaryHeap<State> = BinaryHeap::new();
                let init_state = (State {
                    grid: grid,
                    placed,
                    ..Default::default()
                })
                .fill_by_grid_and_placed();
                to_visit.push(init_state);
                while let Some(state) = to_visit.pop() {
                    if state.placed == *required {
                        return true;
                    }
                    for (si, shape) in self.shapes.iter().enumerate() {
                        if required[si] == state.placed[si] {
                            continue;
                        }
                        'next_variant: for variant in shape.3.iter() {
                            // place the best place that makes the filled region compact
                            for d in 0..height + width {
                                let mut found = false;
                                for i in 0..=d {
                                    let y = i;
                                    let x = d - i;
                                    if let Some(grid) = not_overlapped(&state.grid, (y, x), variant)
                                    {
                                        let mut placed = state.placed.clone();
                                        placed[si] += 1;
                                        let new_state = (State {
                                            grid,
                                            placed,
                                            ..Default::default()
                                        })
                                        .fill_by_grid_and_placed();
                                        to_visit.push(new_state);
                                        found = true;
                                    }
                                }
                                if found {
                                    continue 'next_variant;
                                }
                            }
                        }
                    }
                }
                // to_visit = next.into_iter().collect::<BinaryHeap<State>>();
                false
            })
            .count()
    }
    fn part2(&mut self) -> Self::Output2 {
        2025
    }
}

fn possible_directions(shape: &[Vec<bool>]) -> Vec<Vec<Vec<bool>>> {
    let r0 = shape.to_vec();
    let r1 = rotate_clockwise(r0.clone());
    let r1_is_r0 = r1 == r0;
    let r2 = rotate_clockwise(r1.clone());
    let r2_is_r0 = r2 == r0;
    match (r1_is_r0, r2_is_r0) {
        (false, false) => vec![r0.clone(), r1.clone(), rotate_clockwise(r1), rotate_ccw(r0)],
        (false, true) => vec![r0, r1],
        (true, false) => unreachable!(),
        (true, true) => vec![r0],
    }
}

fn not_overlapped(
    grid: &[Vec<bool>],
    pos: Dim2<usize>,
    shape: &[Vec<bool>],
) -> Option<Vec<Vec<bool>>> {
    let grid_height = grid.len();
    let grid_width = grid[0].len();
    let shape_height = shape.len();
    let shape_width = shape[0].len();
    if pos.0 + shape_height > grid_height || pos.1 + shape_width > grid_width {
        return None;
    }
    for y in 0..shape_height {
        for x in 0..shape_width {
            if shape[y][x] && grid[pos.0 + y][pos.1 + x] {
                return None;
            }
        }
    }
    let mut g = grid.to_vec().clone();
    for y in 0..shape_height {
        for x in 0..shape_width {
            if shape[y][x] {
                g[pos.0 + y][pos.1 + x] = true;
            }
        }
    }
    Some(g)
}
