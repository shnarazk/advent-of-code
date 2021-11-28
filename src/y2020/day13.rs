use crate::{Description, ProblemObject, ProblemSolver};

pub fn day13(part: usize, desc: Description) {
    dbg!(Setting::parse(desc).run(part));
}

#[derive(Debug, PartialEq)]
struct Object {
    time: usize,
    bus: Vec<(usize, usize)>,
}

impl ProblemObject for Object {
    fn parse(s: &str) -> Option<Self> {
        let mut bus: Vec<(usize, usize)> = Vec::new();
        let mut iter = s.split('\n');
        let time = iter.next().unwrap().parse::<usize>().unwrap();
        for (i, b) in iter.next().unwrap().split(',').enumerate() {
            if let Ok(n) = b.parse::<usize>() {
                bus.push((n, i));
            }
        }
        Some(Object { time, bus })
    }
}

#[derive(Debug, PartialEq)]
struct Setting {
    time: usize,
    bus: Vec<(usize, usize)>,
}

impl ProblemSolver<Object, usize, usize> for Setting {
    const YEAR: usize = 2020;
    const DAY: usize = 13;
    const DELIMITER: &'static str = "\n\n";
    fn default() -> Self {
        Setting {
            time: 0,
            bus: Vec::new(),
        }
    }
    fn insert(&mut self, mut object: Object) {
        std::mem::swap(&mut self.time, &mut object.time);
        std::mem::swap(&mut self.bus, &mut object.bus);
    }
    fn part1(&mut self) -> usize {
        let mut bus: usize = self.bus[0].0;
        let mut wait = usize::MAX;
        for (cycle, _) in self.bus.iter() {
            let before = self.time % cycle;
            if before == 0 {
                return 0;
            }
            let w = cycle - before;
            if w < wait {
                wait = w;
                bus = *cycle;
            }
        }
        wait * bus
    }
    fn part2(&mut self) -> usize {
        let mut x = self.bus[0];
        for tuple in self.bus.iter().skip(1) {
            let offset = if tuple.1 <= tuple.0 {
                tuple.0 - tuple.1
            } else {
                println!("逆転{}, {}", tuple.0, tuple.1);
                (tuple.0 * tuple.1 - tuple.1) % tuple.0
            };
            println!("周期{}で{}余る", tuple.0, offset);
            x = chinese(x, (tuple.0, offset));
            //assert_eq!(tuple.0 - x.1 % tuple.0, tuple.1);
        }
        x.1
    }
}

/// Return `x` such that:
/// * x `mod` aq = am
/// * x `mod` bq = bm
///
/// ```
/// use crate::adventofcode2020::day13::*;
/// let a = chinese((3, 2), (5, 3));
/// assert_eq!(a.1, 8);
/// let b = chinese(a, (2, 7));
/// assert_eq!(b.1, 23);
/// ```
pub fn chinese((aq, ar): (usize, usize), (bq, br): (usize, usize)) -> (usize, usize) {
    let n = solve1(aq, bq);
    let nar = (n * ar) % bq;
    let nbr = (n * br) % bq;
    let m = if nar < nbr {
        nbr - nar
    } else {
        (bq + nbr) - nar
    };
    (aq * bq, aq * m + ar)
}

/// Return `X` such that:
/// (X * a) `mod` m = ((X * b) `mod` m) + 1
///
fn solve1(a: usize, m: usize) -> usize {
    for i in 0.. {
        if (i * a) % m == 1 {
            return i;
        }
    }
    panic!("can't");
}

#[cfg(test)]
mod test {
    use {
        super::*,
        crate::{Answer, Description},
    };

    #[test]
    fn test_chinese() {
        let a = chinese((3, 2), (5, 3));
        assert_eq!(a.1, 8);
        let c = chinese(a, (2, 7));
        assert_eq!(c.1, 23);
    }

    #[test]
    fn test_part1() {
        assert_eq!(
            Setting::parse(Description::FileTag("test".to_string())).run(1),
            Answer::Part1(295)
        );
    }
    #[test]
    fn test_part2() {
        assert_eq!(
            Setting::parse(Description::FileTag("test".to_string())).run(2),
            Answer::Part2(1068781)
        );
    }
}
