//! <https://adventofcode.com/2020/day/16>
use crate::framework::{AdventOfCode, ParseError, aoc};

type Range = (String, usize, usize, usize, usize);

#[derive(Clone, Debug, Default, PartialEq)]
pub struct Puzzle {
    dic: Vec<Range>,
    samples: Vec<Vec<usize>>,
    ticket: Vec<usize>,
    field_cands: Vec<Vec<Range>>,
    good_samples: Vec<Vec<usize>>,
}

mod parser {
    use {
        super::Range,
        crate::parser::parse_usize,
        winnow::{
            ModalResult, Parser,
            ascii::newline,
            combinator::{separated, seq},
            token::take_until,
        },
    };

    fn parse_range(str: &mut &str) -> ModalResult<Range> {
        seq!(
            take_until(1.., ": "),
            _: ": ",
            parse_usize,
            _: "-",
            parse_usize,
            _: " or ",
            parse_usize,
            _: "-",
            parse_usize,
        )
        .map(|(name, a, b, c, d)| (name.to_string(), a, b, c, d))
        .parse_next(str)
    }

    fn parse_number_line(s: &mut &str) -> ModalResult<Vec<usize>> {
        separated(1.., parse_usize, ",").parse_next(s)
    }

    #[allow(clippy::type_complexity)]
    pub fn parse(s: &mut &str) -> ModalResult<(Vec<Range>, Vec<usize>, Vec<Vec<usize>>)> {
        seq!(
            separated(1.., parse_range, newline),
            _: "\n\nyour ticket:\n",
            parse_number_line,
            _: "\n\nnearby tickets:\n",
            separated(1.., parse_number_line, newline)
        )
        .parse_next(s)
    }
}

#[aoc(2020, 16)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, mut input: &str) -> Result<(), ParseError> {
        let (range, ticket, nearby) = parser::parse(&mut input)?;
        self.dic = range;
        self.ticket = ticket;
        self.samples = nearby;
        // build cands
        for field in &self.ticket {
            let mut res: Vec<Range> = Vec::new();
            for pair in &self.dic {
                if valid(pair, *field) {
                    res.push(pair.clone());
                }
            }
            self.field_cands.push(res);
        }
        Self::parsed()
    }
    fn part1(&mut self) -> usize {
        // dbg!(&field_cands);
        let mut count = 0;
        for v in &self.samples {
            let mut ok = true;
            for (i, e) in v.iter().enumerate() {
                if let Some(n) = invalid(&self.field_cands[i], *e) {
                    // println!(
                    //     "{}th element {} is out of range {:?}",
                    //     i, e, &self.field_cands[i]
                    // );
                    count += n;
                    ok = false;
                }
            }
            if ok {
                // println!("is good");
                self.good_samples.push(v.clone());
            }
        }
        count
    }
    fn part2(&mut self) -> usize {
        self.part1();
        let mut result: Vec<Vec<(String, usize)>> = Vec::new();
        for (i, ranges) in self.field_cands.iter().enumerate() {
            let mut valids: Vec<(String, usize)> = Vec::new();
            for range in ranges {
                if self
                    .good_samples
                    .iter()
                    .all(|sample| valid(range, sample[i]))
                {
                    valids.push((range.0.clone(), self.ticket[i]));
                }
            }
            // println!(
            //     "{}-th field ({}) has {} cands: {:?}",
            //     i,
            //     self.ticket[i],
            //     valids.len(),
            //     valids.iter().map(|r| &r.0).collect::<Vec<_>>(),
            // );
            result.push(valids);
        }
        // simplify
        let mut trimmed: Vec<(String, usize)> = Vec::new();
        loop {
            let mut index: Option<usize> = None;
            for (i, cands) in result.iter().enumerate() {
                if cands.len() == 1 {
                    index = Some(i);
                    break;
                }
            }
            if let Some(n) = index {
                let name: String = result[n][0].0.clone();
                trimmed.push(result[n][0].clone());
                // println!("asserted {}", name);
                for v in result.iter_mut() {
                    v.retain(|range| range.0 != name);
                }
            } else {
                break;
            }
        }
        let mut count = 1;
        for r in &trimmed {
            if r.0.contains("departure") {
                // println!("{}:\t{}", r.0, r.1);
                count *= r.1;
            }
        }
        count
    }
}

fn valid((_, a, b, c, d): &Range, val: usize) -> bool {
    (*a <= val && val <= *b) || (*c <= val && val <= *d)
}

fn invalid(dic: &[Range], x: usize) -> Option<usize> {
    if dic
        .iter()
        .any(|(_, a, b, c, d)| (*a <= x && x <= *b) || (*c <= x && x <= *d))
    {
        None
    } else {
        Some(x)
    }
}
