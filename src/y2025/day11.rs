//! <https://adventofcode.com/2025/day/11>
use {
    crate::framework::{AdventOfCode, ParseError, aoc},
    rustc_data_structures::fx::{FxHashMap, FxHasher},
    std::{collections::HashMap, hash::BuildHasherDefault},
};

#[derive(Clone, Debug, Default)]
pub struct Puzzle {
    // line: Vec<(String, Vec<String>)>,
    name: FxHashMap<String, usize>,
    flow: FxHashMap<usize, Vec<usize>>,
    dist: FxHashMap<(usize, usize), usize>,
}

mod parser {
    use winnow::{
        ModalResult, Parser,
        ascii::{alpha1, newline},
        combinator::{separated, seq},
    };

    fn parse_name(s: &mut &str) -> ModalResult<String> {
        alpha1.map(|s: &str| s.to_string()).parse_next(s)
    }

    fn parse_line(s: &mut &str) -> ModalResult<(String, Vec<String>)> {
        seq!(parse_name, _: ": ", separated(1.., parse_name, " ")).parse_next(s)
    }

    pub fn parse(s: &mut &str) -> ModalResult<Vec<(String, Vec<String>)>> {
        separated(1.., parse_line, newline).parse_next(s)
    }
}

#[aoc(2025, 11)]
impl AdventOfCode for Puzzle {
    fn prepare(&mut self, mut input: &str) -> Result<(), ParseError> {
        let line = parser::parse(&mut input)?;
        dbg!(line.len());
        self.name = HashMap::<_, _, BuildHasherDefault<FxHasher>>::default();
        self.flow = HashMap::<_, _, BuildHasherDefault<FxHasher>>::default();
        self.dist = HashMap::<_, _, BuildHasherDefault<FxHasher>>::default();
        for (s, outs) in line.iter() {
            if !self.name.contains_key(s) {
                self.name.insert(s.to_string(), self.name.len());
            }
            for out in outs {
                if !self.name.contains_key(out) {
                    self.name.insert(out.to_string(), self.name.len());
                }
                self.flow
                    .entry(*self.name.get(s).unwrap())
                    .or_default()
                    .push(*self.name.get(out).unwrap());
                self.dist.insert(
                    (*self.name.get(s).unwrap(), *self.name.get(out).unwrap()),
                    1,
                );
            }
        }
        dbg!(&self.flow.len());
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        count_pathes(
            &self.flow,
            *self.name.get("you").unwrap(),
            *self.name.get("out").unwrap(),
            &mut self.dist,
        )
    }
    fn part2(&mut self) -> Self::Output2 {
        let dac_fft = count_pathes(
            &self.flow,
            *self.name.get("dac").unwrap(),
            *self.name.get("fft").unwrap(),
            &mut self.dist,
        );
        if dac_fft > 0 {
            count_pathes(
                &self.flow,
                *self.name.get("svr").unwrap(),
                *self.name.get("dac").unwrap(),
                &mut self.dist,
            ) * dac_fft
                * count_pathes(
                    &self.flow,
                    *self.name.get("dac").unwrap(),
                    *self.name.get("out").unwrap(),
                    &mut self.dist,
                )
        } else {
            count_pathes(
                &self.flow,
                *self.name.get("svr").unwrap(),
                *self.name.get("fft").unwrap(),
                &mut self.dist,
            ) * count_pathes(
                &self.flow,
                *self.name.get("fft").unwrap(),
                *self.name.get("dac").unwrap(),
                &mut self.dist,
            ) * count_pathes(
                &self.flow,
                *self.name.get("dac").unwrap(),
                *self.name.get("out").unwrap(),
                &mut self.dist,
            )
        }
    }
}

fn count_pathes(
    flow: &FxHashMap<usize, Vec<usize>>,
    from: usize,
    to: usize,
    dist: &mut FxHashMap<(usize, usize), usize>,
) -> usize {
    if let Some(n) = dist.get(&(from, to)) {
        return *n;
    }
    let n = flow
        .get(&from)
        .unwrap_or(&vec![])
        .iter()
        .map(|&t| count_pathes(flow, t, to, dist))
        .sum::<usize>();
    dist.insert((from, to), n);
    n
}
