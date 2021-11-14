use {
    crate::{Description, ProblemSolver},
    std::collections::HashSet,
};

pub fn day09(part: usize, desc: Description) {
    if desc == Description::FileTag("test1".to_string()) {
        dbg!(Setting::parse(desc).set_len(5).run(part));
    } else {
        dbg!(Setting::parse(desc).run(part));
    }
}

#[derive(Debug, PartialEq)]
struct Setting {
    vec: Vec<usize>,
    len: usize,
}

impl ProblemSolver<usize, usize, usize> for Setting {
    const DAY: usize = 9;
    const DELIMITER: &'static str = "\n";
    fn default() -> Self {
        Setting {
            vec: Vec::new(),
            len: 25,
        }
    }
    fn insert(&mut self, n: usize) {
        self.vec.push(n);
    }
    fn part1(&mut self) -> usize {
        let len = self.len;
        let mut set: HashSet<usize> = HashSet::new();
        for n in &self.vec[..len] {
            set.insert(*n);
        }
        for (i, n) in self.vec.iter().enumerate().skip(len) {
            let out = self.vec[i - len];
            let mut found = false;
            for k in &set {
                if 2 * *k < *n && set.contains(&(*n - *k)) {
                    found = true;
                    break;
                }
            }
            if found {
                set.remove(&out);
                assert!(!set.contains(&out));
                if !set.insert(*n) {
                    panic!("this requires HashMap");
                }
                assert!(set.contains(n));
            } else {
                return *n;
            }
        }
        0
    }
    fn part2(&mut self) -> usize {
        let len = self.vec.len();
        let magic_number = self.part1();
        'next: for start in 0..len {
            let mut sum = 0;
            for i in start..len {
                sum += self.vec[i];
                if sum == magic_number {
                    let mn = *self.vec[start..i].iter().min().unwrap();
                    let mx = *self.vec[start..i].iter().max().unwrap();
                    return mn + mx;
                }
                if magic_number < sum {
                    continue 'next;
                }
            }
        }
        0
    }
}

impl Setting {
    fn set_len(&mut self, n: usize) -> &mut Setting {
        self.len = n;
        self
    }
}

#[cfg(test)]
mod test {
    use {
        super::*,
        crate::{Answer, Description},
    };

    #[test]
    fn test_part1() {
        assert_eq!(
            Setting::parse(Description::FileTag("test1".to_string()))
                .set_len(5)
                .run(1),
            Answer::Part1(127)
        );
    }
    #[test]
    fn test_part2() {
        assert_eq!(
            Setting::parse(Description::FileTag("test1".to_string()))
                .set_len(5)
                .run(2),
            Answer::Part2(62)
        );
    }
}
