use crate::y2020::traits::{Description, ProblemObject, ProblemSolver};

pub fn day01(part: usize, desc: Description) {
    dbg!(Setting::parse(desc).run(part));
}

impl ProblemObject for usize {
    fn parse(s: &str) -> Option<Self> {
        s.parse::<usize>().ok()
    }
}

#[derive(Debug, PartialEq)]
struct Setting {
    val: Vec<usize>,
}

impl ProblemSolver<usize, usize, usize> for Setting {
    const YEAR: usize = 2020;
    const DAY: usize = 1;
    const DELIMITER: &'static str = "\n";
    fn default() -> Self {
        Setting { val: Vec::new() }
    }
    fn insert(&mut self, n: usize) {
        self.val.push(n);
    }
    fn part1(&mut self) -> usize {
        for i in &self.val {
            for j in &self.val {
                if i + j == 2020 {
                    return i * j;
                }
            }
        }
        0
    }
    fn part2(&mut self) -> usize {
        for (i, x) in self.val.iter().enumerate() {
            for (j, y) in self.val.iter().enumerate().skip(i) {
                for z in self.val.iter().skip(j) {
                    if x + y + z == 2020 {
                        return x * y * z;
                    }
                }
            }
        }
        0
    }
}

#[cfg(feature = "y2020")]
#[cfg(test)]
mod test {
    use {
        super::*,
        crate::y2020::traits::{Answer, Description},
    };

    const TEST: &str = "\
1721
979
366
299
675
1456";

    #[test]
    fn test1() {
        assert_eq!(
            Setting::parse(Description::TestData(TEST.to_string())).run(1),
            Answer::Part1(514579)
        );
    }

    #[cfg_attr(feature = "y2020", test)]
    fn test2() {
        assert_eq!(
            Setting::parse(Description::TestData(TEST.to_string())).run(2),
            Answer::Part2(241861950)
        );
    }
}
