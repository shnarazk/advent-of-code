//! <https://adventofcode.com/2016/day/22>
use {
    crate::framework::{AdventOfCode, ParseError, aoc},
    std::collections::{HashSet, binary_heap::BinaryHeap},
};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<(usize, usize, usize, usize, usize, usize)>,
}

mod parser {
    use {
        crate::parser::parse_usize,
        winnow::{
            ModalResult, Parser,
            ascii::{newline, space1},
            combinator::{repeat_till, separated, seq},
            token::any,
        },
    };

    #[allow(clippy::type_complexity)]
    fn parse_line(s: &mut &str) -> ModalResult<(usize, usize, usize, usize, usize, usize)> {
        seq!(
            _: "/dev/grid/node-x", parse_usize, _: "-y", parse_usize, _: space1,
            parse_usize, _: ("T", space1),
            parse_usize, _: ("T", space1),
            parse_usize, _: ("T", space1),
            parse_usize, _: "%",
        )
        .map(|(a, b, c, d, e, f)| (b, a, c, d, e, f))
        .parse_next(s)
    }

    #[allow(clippy::type_complexity)]
    pub fn parse(s: &mut &str) -> ModalResult<Vec<(usize, usize, usize, usize, usize, usize)>> {
        seq!(
            _: (
                repeat_till(1.., any, newline).map(|_: (Vec<char>, char)| ()),
                repeat_till(1.., any, newline).map(|_: (Vec<char>, char)| ()),
            ),
            separated(1.., parse_line, newline)
        )
        .map(|(v,)| v)
        .parse_next(s)
    }
}

#[aoc(2016, 22)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, mut input: &str) -> Result<(), ParseError> {
        self.line = parser::parse(&mut input)?;
        self.line.sort_unstable();
        let mut w = 0;
        for cell in self.line.iter() {
            w = w.max(cell.1);
        }
        let width = w + 1;
        for (i, site) in self.line.iter().enumerate() {
            debug_assert_eq!(i, site.0 * width + site.1);
        }
        Self::parsed()
    }
    fn part1(&mut self) -> Self::Output1 {
        self.line.sort_unstable_by_key(|line| line.4);
        let mut count = 0;
        for (i, dev) in self.line.iter().enumerate() {
            for (j, other) in self.line.iter().enumerate() {
                if 0 < dev.3 && i != j && dev.3 <= other.4 {
                    count += 1;
                }
            }
        }
        count
    }
    fn part2(&mut self) -> Self::Output2 {
        type State = Vec<usize>;
        let mut w = 0;
        let mut h = 0;
        for cell in self.line.iter() {
            h = h.max(cell.0);
            w = w.max(cell.1);
        }
        let width = w + 1;
        let height = h + 1;
        // dbg!(width, height);
        debug_assert_eq!(width * height, self.line.len());
        let mut to_visit: BinaryHeap<(isize, usize, State, usize)> = BinaryHeap::new();
        let mut visited: HashSet<(State, usize)> = HashSet::new();
        let init = self.line.iter().map(|site| site.3).collect::<Vec<usize>>();
        let mut check: isize = -1_000_000;
        to_visit.push((check + 1, 0, init, width - 1));
        while let Some((a_star, cost, state, goal)) = to_visit.pop() {
            debug_assert!(visited.len() < 1_000_000);
            let empty = state
                .iter()
                .enumerate()
                .find(|(_, used)| **used == 0)
                .unwrap()
                .0;
            // if (-1400 < check && check < a_star + cost as isize) || 0 == goal {
            //     for (i, c) in state.iter().enumerate() {
            //         if i == goal {
            //             print!("G{:>2},", *c);
            //         } else if *c == 0 {
            //             print!("  _,");
            //         } else {
            //             print!("{:>3},", *c);
            //         }
            //         if (i + 1) % width == 0 {
            //             println!();
            //         }
            //     }
            //     dbg!(cost);
            // }
            check = check.max(a_star + cost as isize);

            if 0 == goal {
                return cost;
            }
            let mut neighbors: Vec<(usize, Vec<usize>)> = Vec::new();
            macro_rules! ADD {
                ($pos: expr) => {
                    let mut new = state.clone();
                    new.swap(empty, $pos);
                    let new_goal = if $pos == goal { empty } else { goal };
                    if !visited.contains(&(new.clone(), new_goal)) {
                        neighbors.push(($pos, new));
                    }
                };
            }
            // Up
            if width <= empty && state[empty - width] <= self.line[empty].2 {
                ADD!(empty - width);
            };
            // Down
            if empty + width < self.line.len() && state[empty + width] <= self.line[empty].2 {
                ADD!(empty + width);
            };
            // Left
            if 0 < empty % width && state[empty - 1] <= self.line[empty].2 {
                ADD!(empty - 1);
            };
            // Right
            if 0 < (empty + 1) % width && state[empty + 1] <= self.line[empty].2 {
                ADD!(empty + 1);
            };
            while let Some((index, neighbor)) = neighbors.pop() {
                let new_goal = if index == goal { empty } else { goal };
                let a_star = if 17 < index / width {
                    10000 + ((index % width).abs_diff(1) + (index / width).abs_diff(0))
                } else if new_goal == width - 1 {
                    1000 + ((index % width).abs_diff((new_goal % width).saturating_sub(1))
                        + (index / width).abs_diff(new_goal / width))
                } else {
                    5 * ((new_goal % width) + (new_goal / width))
                };
                to_visit.push((
                    -((cost + 1 + a_star) as isize),
                    cost + 1,
                    neighbor,
                    new_goal,
                ));
            }
            visited.insert((state, goal));
        }
        0
    }
}
