use crate::y2020::traits::{Description, ProblemObject, ProblemSolver};

pub fn day11(part: usize, desc: Description) {
    dbg!(World::parse(desc).run(part));
}

#[derive(Clone, Debug, PartialEq)]
struct Chars {
    char: Vec<char>,
}

impl ProblemObject for Chars {
    fn parse(s: &str) -> Option<Self> {
        if s.is_empty() {
            None
        } else {
            Some(Chars {
                char: s.chars().collect::<Vec<char>>(),
            })
        }
    }
}

#[derive(Debug, PartialEq)]
struct World {
    data: Vec<Chars>,
    size: usize,
}

impl ProblemSolver<Chars, usize, usize> for World {
    const YEAR: usize = 2020;
    const DAY: usize = 11;
    const DELIMITER: &'static str = "\n";
    fn default() -> Self {
        World {
            data: Vec::new(),
            size: 0,
        }
    }
    fn insert(&mut self, cs: Chars) {
        self.data.push(cs);
    }
    fn part1(&mut self) -> usize {
        loop {
            let next = self.next1();
            if self.data == next {
                return self.num_occupied();
            }
            self.data = next;
        }
    }
    fn part2(&mut self) -> usize {
        loop {
            let next = self.next2();
            if self.data == next {
                return self.num_occupied();
            }
            self.data = next;
        }
    }
}

impl World {
    fn at(&self, i: usize, j: usize) -> char {
        self.data[i].char[j]
    }
    fn neighbors(&self, i: usize, j: usize) -> Vec<char> {
        let mut vec: Vec<char> = Vec::new();
        for oi in &[-1, 0, 1] {
            if (0 == i && *oi == -1) || (i == self.data.len() - 1 && *oi == 1) {
                continue;
            }
            for oj in &[-1, 0, 1] {
                if (0 == j && *oj == -1) || (j == self.data[0].char.len() - 1 && *oj == 1) {
                    continue;
                }
                if *oi == 0 && *oj == 0 {
                    continue;
                }
                vec.push(self.data[(i as isize + oi) as usize].char[((j as isize) + oj) as usize]);
            }
        }
        vec
    }
    fn with_offset(&self, i: usize, j: usize, oi: isize, oj: isize) -> Option<char> {
        let ii: isize = i as isize + oi;
        let jj: isize = j as isize + oj;
        if ii < 0
            || self.data.len() as isize <= ii
            || jj < 0
            || self.data[0].char.len() as isize <= jj
        {
            return None;
        }
        Some(self.at(ii as usize, jj as usize))
    }
    fn num_occupied(&self) -> usize {
        self.data
            .iter()
            .map(|cs| cs.char.iter().filter(|c| **c == '#').count())
            .sum()
    }
    fn num_occupied_around(&self, i: usize, j: usize) -> usize {
        self.neighbors(i, j).iter().filter(|c| **c == '#').count()
    }
    fn find_around_through(
        &self,
        c: char,
        blockers: &[char],
        bi: usize,
        bj: usize,
        ii: isize,
        jj: isize,
    ) -> bool {
        let mut scale: isize = 1;
        while let Some(v) = self.with_offset(bi, bj, ii * scale, jj * scale) {
            if v == c {
                return true;
            }
            if blockers.contains(&v) {
                return false;
            }
            scale += 1;
        }
        false
    }
    fn num_occupied_around_through(&self, i: usize, j: usize) -> usize {
        let dirs = [
            (-1, 0),
            (-1, 1),
            (0, 1),
            (1, 1),
            (1, 0),
            (1, -1),
            (0, -1),
            (-1, -1),
        ];
        dirs.iter()
            .filter(|(oi, oj)| self.find_around_through('#', &['L'], i, j, *oi, *oj))
            .count()
    }

    fn next1(&mut self) -> Vec<Chars> {
        let mut v: Vec<Chars> = self.data.clone();
        let len = self.data[0].char.len();
        for (i, vi) in v.iter_mut().enumerate() {
            for j in 0..len {
                let no = self.num_occupied_around(i, j);
                match self.at(i, j) {
                    'L' if no == 0 => vi.char[j] = '#',
                    '#' if 4 <= no => vi.char[j] = 'L',
                    _ => (),
                }
            }
        }
        v
    }
    fn next2(&mut self) -> Vec<Chars> {
        let mut v: Vec<Chars> = self.data.clone();
        for (i, vi) in v.iter_mut().enumerate() {
            for j in 0..self.data[0].char.len() {
                let no = self.num_occupied_around_through(i, j);
                match self.at(i, j) {
                    'L' if no == 0 => vi.char[j] = '#',
                    '#' if 5 <= no => vi.char[j] = 'L',
                    _ => (),
                }
            }
        }
        v
    }
}

#[cfg(feature = "y2020")]
#[cfg(test)]
mod test {
    use {
        super::*,
        crate::y2020::traits::{Answer, Description},
    };

    #[test]
    fn test_part1() {
        assert_eq!(
            World::parse(Description::FileTag("test1".to_string())).run(1),
            Answer::Part1(37)
        );
    }
    #[test]
    fn test_part2() {
        assert_eq!(
            World::parse(Description::FileTag("test1".to_string())).run(2),
            Answer::Part2(26)
        );
    }
}
