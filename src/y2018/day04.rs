//! <https://adventofcode.com/2018/day/4>
use {
    crate::framework::{AdventOfCode, ParseError, aoc},
    std::collections::{HashMap, HashSet},
};

#[derive(Copy, Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Timestamp {
    year: usize,
    month: usize,
    day: usize,
    hour: usize,
    min: usize,
}

impl Timestamp {
    fn as_day(&self) -> Day {
        Day {
            year: self.year,
            month: self.month,
            day: self.day,
        }
    }
}

#[derive(Copy, Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Day {
    year: usize,
    month: usize,
    day: usize,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Record {
    Start(Timestamp, usize),
    Sleep(Timestamp, usize),
    Wake_(Timestamp, usize),
}

impl Record {
    fn timestamp(&self) -> Timestamp {
        match self {
            Record::Start(ts, _) => *ts,
            Record::Sleep(ts, _) => *ts,
            Record::Wake_(ts, _) => *ts,
        }
    }
}

#[derive(Clone, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Record>,
}

mod parser {
    use {
        super::*,
        crate::parser::{parse_ndigits, parse_usize},
        winnow::{
            ModalResult, Parser,
            ascii::newline,
            combinator::{alt, separated, seq},
        },
    };

    fn parse_timestamp(s: &mut &str) -> ModalResult<Timestamp> {
        seq!(
            _: "[", parse_ndigits(4),
            _: "-", parse_ndigits(2),
            _: "-", parse_ndigits(2),
            _: " ", parse_ndigits(2),
            _: ":", parse_ndigits(2),
            _: "]")
        .map(|(a, b, c, d, e)| Timestamp {
            year: a,
            month: b,
            day: c,
            hour: d,
            min: e,
        })
        .parse_next(s)
    }
    fn parse_record(s: &mut &str) -> ModalResult<Record> {
        alt((
            seq!(parse_timestamp, _: " Guard #", parse_usize, _: " begins shift")
                .map(|(t, n): (Timestamp, usize)| Record::Start(t, n)),
            seq!(parse_timestamp, _: " falls asleep").map(|(t,)| Record::Sleep(t, t.min)),
            seq!(parse_timestamp, _: " wakes up").map(|(t,)| Record::Wake_(t, t.min)),
        ))
        .parse_next(s)
    }

    pub fn parse(s: &mut &str) -> ModalResult<Vec<Record>> {
        separated(1.., parse_record, newline).parse_next(s)
    }
}

#[aoc(2018, 4)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, mut input: &str) -> Result<(), ParseError> {
        self.line = parser::parse(&mut input)?;
        self.line.sort_by_key(|e| e.timestamp());
        Self::parsed()
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut guard: Option<usize> = None;
        let mut beg: Option<usize> = None;
        let mut total: HashMap<usize, usize> = HashMap::new();
        let mut days: HashMap<usize, HashSet<Day>> = HashMap::new();
        for r in self.line.iter() {
            match r {
                Record::Start(_ts, g) => {
                    guard = Some(*g);
                }
                Record::Sleep(_ts, b) => {
                    beg = Some(*b);
                }
                Record::Wake_(ts, e) => {
                    if let Some(g) = guard {
                        if let Some(b) = beg {
                            if *e < b {
                                panic!();
                            }
                            *total.entry(g).or_insert(0) += e - b;
                            days.entry(g).or_default().insert(ts.as_day());
                        }
                    }
                    beg = None;
                }
            }
        }
        // dbg!(&total);
        let mut len_max: f64 = 0.0;
        let mut id_max: usize = 0;
        for (guard_id, val) in total.iter() {
            let n_days = days.get(guard_id).unwrap();
            let v = *val as f64 / (n_days.len() as f64);
            if len_max < v {
                len_max = v;
                id_max = *guard_id;
            }
        }
        let mut minute = [0_usize; 60];
        for r in self.line.iter() {
            match r {
                Record::Start(_ts, g) => {
                    guard = Some(*g);
                }
                Record::Sleep(_ts, b) => {
                    beg = Some(*b);
                }
                Record::Wake_(_ts, e) => {
                    if guard == Some(id_max) {
                        if let Some(b) = beg {
                            for p in &mut minute[b..*e] {
                                *p += 1;
                            }
                        }
                    }
                    beg = None;
                }
            }
        }
        // dbg!(&minute);
        let mut minute_max = 0;
        let mut occurs_max = 0;
        for (i, o) in minute.iter().enumerate() {
            if occurs_max < *o {
                occurs_max = *o;
                minute_max = i;
            }
        }
        id_max * minute_max
    }
    fn part2(&mut self) -> Self::Output1 {
        let mut guard: Option<usize> = None;
        let mut beg: Option<usize> = None;
        let mut total: HashMap<usize, usize> = HashMap::new();
        let mut minite_report: HashMap<usize, [usize; 60]> = HashMap::new();
        for r in self.line.iter() {
            match r {
                Record::Start(_ts, g) => {
                    guard = Some(*g);
                }
                Record::Sleep(_ts, b) => {
                    beg = Some(*b);
                }
                Record::Wake_(_ts, e) => {
                    if let Some(g) = guard {
                        if let Some(b) = beg {
                            debug_assert!(b < *e);
                            *total.entry(g).or_insert(0) += e - b;
                            for t in b..*e {
                                minite_report.entry(g).or_insert([0; 60])[t] += 1;
                            }
                        }
                    }
                    beg = None;
                }
            }
        }
        let mut frequent_max: usize = 0;
        let mut result: usize = 0;
        for (guard_id, minites) in minite_report.iter() {
            for (minite, occ) in minites.iter().enumerate() {
                if frequent_max < *occ {
                    frequent_max = *occ;
                    result = *guard_id * minite;
                }
            }
        }
        result
    }
}
