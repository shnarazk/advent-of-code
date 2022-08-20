//! <https://adventofcode.com/2018/day/4>
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        regex,
    },
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

#[derive(Debug, Eq, Ord, PartialEq, PartialOrd)]
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

#[derive(Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Record>,
}

#[aoc(2018, 4)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        //  [1518-06-12 00:00] Guard #1231 begins shift
        //  [1518-03-06 00:56] wakes up
        //  [1518-05-30 00:14] falls asleep
        let begin =
            regex!(r"^\[(\d{4})\-(\d{2})-(\d{2}) (\d{2}):(\d{2})\] Guard #(\d+) begins shift");
        let sleep = regex!(r"^\[(\d{4})-(\d{2})-(\d{2}) (\d{2}):(\d{2})\] falls asleep");
        let wakes = regex!(r"^\[(\d{4})-(\d{2})-(\d{2}) (\d{2}):(\d{2})\] wakes up");
        if let Some(segment) = begin.captures(block) {
            let timestamp = Timestamp {
                year: segment[1].parse::<usize>()?,
                month: segment[2].parse::<usize>()?,
                day: segment[3].parse::<usize>()?,
                hour: segment[4].parse::<usize>()?,
                min: segment[5].parse::<usize>()?,
            };
            self.line
                .push(Record::Start(timestamp, segment[6].parse::<usize>()?));
            return Ok(());
        } else if let Some(segment) = sleep.captures(block) {
            let timestamp = Timestamp {
                year: segment[1].parse::<usize>()?,
                month: segment[2].parse::<usize>()?,
                day: segment[3].parse::<usize>()?,
                hour: segment[4].parse::<usize>()?,
                min: segment[5].parse::<usize>()?,
            };
            self.line
                .push(Record::Sleep(timestamp, segment[5].parse::<usize>()?));
            return Ok(());
        } else if let Some(segment) = wakes.captures(block) {
            let timestamp = Timestamp {
                year: segment[1].parse::<usize>()?,
                month: segment[2].parse::<usize>()?,
                day: segment[3].parse::<usize>()?,
                hour: segment[4].parse::<usize>()?,
                min: segment[5].parse::<usize>()?,
            };
            self.line
                .push(Record::Wake_(timestamp, segment[5].parse::<usize>()?));
            return Ok(());
        }
        Err(ParseError)
    }
    fn after_insert(&mut self) {
        self.line.sort_by_key(|e| e.timestamp());
        dbg!(&self.line.len());
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut guard: Option<usize> = None;
        let mut beg: Option<usize> = None;
        let mut total: HashMap<usize, usize> = HashMap::new();
        let mut days: HashMap<usize, HashSet<Day>> = HashMap::new();
        for (l, r) in self.line.iter().enumerate() {
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
                                for i in l - 2..l + 2 {
                                    println!("{:?}", &self.line[i]);
                                }
                                panic!();
                            }
                            *total.entry(g).or_insert(0) += e - b;
                            days.entry(g)
                                .or_insert_with(HashSet::new)
                                .insert(ts.as_day());
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
                            assert!(b < *e);
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
