//! <https://adventofcode.com/2024/day/12>
use {
    crate::{
        framework::{AdventOfCode, ParseError, aoc},
        geometric::{GeometricMath, Vec2},
        rect::Rect,
    },
    rustc_data_structures::fx::{FxHashMap, FxHashSet, FxHasher},
    serde::Serialize,
    std::{
        collections::{HashMap, HashSet},
        hash::BuildHasherDefault,
    },
    winnow::{
        ModalResult, Parser,
        ascii::{alpha1, newline},
        combinator::separated,
    },
};

#[derive(Clone, Debug, Default, Eq, PartialEq, Serialize)]
pub struct Puzzle {
    mapping: Rect<char>,
}

impl Puzzle {
    fn evaluate1_area(&self, accum: &mut Rect<bool>, pos: Vec2) -> usize {
        if accum[pos] {
            return 0;
        };
        let Some(c) = self.mapping.get(pos) else {
            return 0;
        };
        let mut count = 0;
        let mut r: Rect<Option<bool>> = self.mapping.map(|_| None);
        let mut to_visid: Vec<Vec2> = vec![pos];
        let mut h_segs: FxHashSet<Vec2> = HashSet::<Vec2, BuildHasherDefault<FxHasher>>::default();
        let mut v_segs: FxHashSet<Vec2> = HashSet::<Vec2, BuildHasherDefault<FxHasher>>::default();
        while let Some(p) = to_visid.pop() {
            if let Some(None) = r.get(p) {
                if self.mapping[p] == *c {
                    count += 1;
                    accum[p] = true;
                    r[p] = Some(true);

                    if self.mapping.get((p.0 - 1, p.1)) != Some(c) {
                        h_segs.insert(p);
                    }
                    if self.mapping.get((p.0 + 1, p.1)) != Some(c) {
                        h_segs.insert((p.0 + 1, p.1));
                    }
                    if self.mapping.get((p.0, p.1 - 1)) != Some(c) {
                        v_segs.insert(p);
                    }
                    if self.mapping.get((p.0, p.1 + 1)) != Some(c) {
                        v_segs.insert((p.0, p.1 + 1));
                    }

                    for q in p.neighbors4((0, 0), self.mapping.size()).iter() {
                        to_visid.push(*q);
                    }
                } else {
                    r[p] = Some(false);
                }
            }
        }
        // println!("({pos:?}) => area: {count}, sides: {}", num_hseg + num_vseg);
        count * (v_segs.len() + h_segs.len())
    }
    fn evaluate2_area(&self, accum: &mut Rect<bool>, pos: Vec2) -> usize {
        if accum[pos] {
            return 0;
        };
        let Some(c) = self.mapping.get(pos) else {
            return 0;
        };
        let mut count = 0;
        let mut r: Rect<Option<bool>> = self.mapping.map(|_| None);
        let mut to_visid: Vec<Vec2> = vec![pos];
        let mut h_segs: FxHashSet<(Vec2, bool)> =
            HashSet::<(Vec2, bool), BuildHasherDefault<FxHasher>>::default();
        let mut v_segs: FxHashSet<(Vec2, bool)> =
            HashSet::<(Vec2, bool), BuildHasherDefault<FxHasher>>::default();
        while let Some(p) = to_visid.pop() {
            if let Some(None) = r.get(p) {
                if self.mapping[p] == *c {
                    count += 1;
                    accum[p] = true;
                    r[p] = Some(true);

                    if self.mapping.get((p.0 - 1, p.1)) != Some(c) {
                        h_segs.insert((p, false));
                    }
                    if self.mapping.get((p.0 + 1, p.1)) != Some(c) {
                        h_segs.insert(((p.0 + 1, p.1), true));
                    }
                    if self.mapping.get((p.0, p.1 - 1)) != Some(c) {
                        v_segs.insert((p, false));
                    }
                    if self.mapping.get((p.0, p.1 + 1)) != Some(c) {
                        v_segs.insert(((p.0, p.1 + 1), true));
                    }

                    for q in p.neighbors4((0, 0), self.mapping.size()).iter() {
                        to_visid.push(*q);
                    }
                } else {
                    r[p] = Some(false);
                }
            }
        }
        // build longer segment
        let hss: FxHashMap<usize, Vec<(usize, bool)>> = h_segs.iter().fold(
            HashMap::<_, _, BuildHasherDefault<FxHasher>>::default(),
            |mut m: FxHashMap<usize, Vec<(usize, bool)>>, &(pos, spin): &((isize, isize), bool)| {
                m.entry(pos.0 as usize)
                    .or_default()
                    .push((pos.1 as usize, spin));
                m
            },
        );
        let vss: FxHashMap<usize, Vec<(usize, bool)>> = v_segs.iter().fold(
            HashMap::<_, _, BuildHasherDefault<FxHasher>>::default(),
            |mut m: FxHashMap<usize, Vec<(usize, bool)>>, &(pos, spin): &((isize, isize), bool)| {
                m.entry(pos.1 as usize)
                    .or_default()
                    .push((pos.0 as usize, spin));
                m
            },
        );

        fn count_sides(hash: FxHashMap<usize, Vec<(usize, bool)>>) -> usize {
            hash.into_values()
                .map(|mut v| {
                    v.sort();
                    let mut num = 1;
                    let mut end = v[0].0 + 1;
                    let mut spin = v[0].1;
                    for &(st, sp) in v.iter().skip(1) {
                        if end != st || spin != sp {
                            num += 1;
                        }
                        end = st + 1;
                        spin = sp;
                    }
                    num
                })
                .sum::<usize>()
        }
        count * (count_sides(hss) + count_sides(vss))
    }
}

fn parse<'a>(s: &'a mut &str) -> ModalResult<Vec<&'a str>> {
    separated(1.., alpha1, newline).parse_next(s)
}

#[aoc(2024, 12)]
impl AdventOfCode for Puzzle {
    fn prepare(&mut self, mut input: &str) -> Result<(), ParseError> {
        let v = parse(&mut input)?;
        self.mapping = Rect::from_vec(
            v.iter()
                .map(|l| l.chars().collect::<Vec<char>>())
                .collect::<Vec<_>>(),
        );
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut accum: Rect<bool> = self.mapping.map(|_| false);
        self.mapping
            .iter()
            .map(|(pos, _)| self.evaluate1_area(&mut accum, pos))
            .sum()
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut accum: Rect<bool> = self.mapping.map(|_| false);
        self.mapping
            .iter()
            .map(|(pos, _)| self.evaluate2_area(&mut accum, pos))
            .sum()
    }
}
