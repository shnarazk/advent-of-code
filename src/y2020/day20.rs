//! <https://adventofcode.com/2020/day/20>
use {
    crate::y2020::traits::{Description, ProblemObject, ProblemSolver},
    lazy_static::lazy_static,
    regex::Regex,
    std::ops::Index,
};

pub fn day20(part: usize, desc: Description) {
    dbg!(Setting::parse(desc).run(part));
}

#[derive(Debug, PartialEq)]
struct Object {}

impl ProblemObject for Tile {
    fn parse(b: &str) -> Option<Tile> {
        lazy_static! {
            static ref RE: Regex = Regex::new(r"^Tile (\d+):$").expect("error");
        }
        let mut lines = b.split('\n').collect::<Vec<_>>();
        if let Some(m) = RE.captures(lines[0]) {
            let id = m[1].parse::<usize>().expect("wrong");
            if let Some(l) = lines.last() {
                if l.is_empty() {
                    lines.pop();
                }
            }
            return Some(Tile::from(id, &lines[1..]));
        }
        None
    }
}

#[derive(Debug, PartialEq)]
struct Setting {
    tile: Vec<Tile>,
}

impl ProblemSolver<Tile, usize, usize> for Setting {
    const YEAR: usize = 2020;
    const DAY: usize = 20;
    const DELIMITER: &'static str = "\n\n";
    fn default() -> Self {
        Setting { tile: Vec::new() }
    }
    fn insert(&mut self, t: Tile) {
        self.tile.push(t);
    }
    fn part1(&mut self) -> usize {
        let p = eval(&self.tile).expect("impossible");
        for (ti, _, _) in p.iter() {
            print!("{:?}, ", ti.id);
        }
        println!();
        let len = self.tile.len();
        let l = (len as f64).sqrt() as usize;
        p[0].0.id * p[l - 1].0.id * p[len - l].0.id * p[len - 1].0.id
    }
    fn part2(&mut self) -> usize {
        let mut p = eval(&self.tile).expect("impossible");
        let len = self.tile.len();
        let l = (len as f64).sqrt() as usize;
        // part 2
        for (t, r, f) in &p {
            print!("({}, {}, {}) ", t.id, r, f);
        }
        println!();
        for i in 0..l {
            for j in 0..l {
                let (ti, r, f) = &p[i * l + j];
                print!("({}, {}, {}) ", ti.id, r, f);
            }
            println!();
        }
        let mut image: Vec<String> = Vec::new();
        let with_border = false;
        for _ in 0..l {
            let mut pasted: Vec<String> = p[0].0.new_empty_image(with_border);
            for _ in 0..l {
                let (ti, r, f) = p.remove(0);
                ti.paste_image(with_border, r, f, &mut pasted);
            }
            for l in &pasted {
                image.push(l.to_string());
            }
        }
        for l in &image {
            println!("{}", l);
        }
        let mut total = 0;
        for rotate in 0..4 {
            for flip in 0..2 {
                let i = transose_image(&image, rotate, flip);
                let n = check_sea_monstar(&i);
                total += n;
            }
        }
        count_sharps(&image) - total * 15
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Tile {
    pub id: usize,
    pub sign: [usize; 4],
    pub len: usize,
    pub image: Vec<String>,
}

pub enum Dir {
    TOP,
    RIGHT,
    BOTTOM,
    LEFT,
}

impl Dir {
    fn as_index(&self) -> usize {
        match self {
            Dir::TOP => 0,
            Dir::RIGHT => 1,
            Dir::BOTTOM => 2,
            Dir::LEFT => 3,
        }
    }
    fn opposite(&self) -> usize {
        match self {
            Dir::TOP => 2,
            Dir::RIGHT => 3,
            Dir::BOTTOM => 0,
            Dir::LEFT => 1,
        }
    }
}

impl Index<Dir> for Tile {
    type Output = usize;
    fn index(&self, dir: Dir) -> &Self::Output {
        match dir {
            Dir::TOP => &self.sign[0],
            Dir::RIGHT => &self.sign[1],
            Dir::BOTTOM => &self.sign[2],
            Dir::LEFT => &self.sign[3],
        }
    }
}

pub fn flip_bits(width: usize, mut n: usize) -> usize {
    let mut result = 0;
    for _ in 0..width {
        result *= 2;
        result += (n % 2) as usize;
        n /= 2;
    }
    result
}

impl Tile {
    /// ```
    /// use adventofcode::y2020::day20::*;
    /// let tile = Tile { id: 0, sign: [1, 1, 1, 1], len: 3, image: Vec::new() };
    /// assert_eq!(tile.transpose(0, 0), [1, 1, 1, 1]);
    /// assert_eq!(tile.transpose(1, 0), [4, 1, 4, 1]);
    /// assert_eq!(tile.transpose(2, 0), [4, 4, 4, 4]);
    /// assert_eq!(tile.transpose(3, 0), [1, 4, 1, 4]);
    /// assert_eq!(tile.transpose(0, 1), [4, 1, 4, 1]);
    /// let t = Tile {id: 2473, sign: [542, 116, 234, 966], len: 10, image: Vec::new() };
    /// assert_eq!(t.transpose(0, 0), [542, 116, 234, 966]);
    /// assert_eq!(format!("{:#b}", flip_bits(10, 542)), format!("{:#b}", 481));
    /// assert_eq!(t.transpose(1, 0), [399, 542, 184, 234]);
    /// assert_eq!(t.transpose(0, 1), [481, 966, 348, 116]);
    /// assert_eq!(t.transpose(1, 1), [966, 234, 116, 542]);
    /// ```
    pub fn transpose(&self, n: usize, flip: usize) -> [usize; 4] {
        let rot = |x, r| {
            if r {
                flip_bits(self.len, x)
            } else {
                x
            }
        };
        // rotate part
        let mut result = [0; 4];
        result[0] = rot(self.sign[(4 - n) % 4], 1 == n || 2 == n);
        result[1] = rot(self.sign[(5 - n) % 4], 2 == n || 3 == n);
        result[2] = rot(self.sign[(6 - n) % 4], 1 == n || 2 == n);
        result[3] = rot(self.sign[(7 - n) % 4], 2 == n || 3 == n);
        // horizontal flip
        if flip % 2 == 1 {
            result.swap(1, 3);
            result[0] = flip_bits(self.len, result[0]);
            result[2] = flip_bits(self.len, result[2]);
        }
        // vertial flip
        if flip / 2 == 1 {
            result.swap(0, 2);
            result[1] = flip_bits(self.len, result[1]);
            result[3] = flip_bits(self.len, result[3]);
        }
        result
    }
    pub fn valid(
        &self,
        align: usize,
        rotate: usize,
        flip: usize,
        placed: &[(Tile, usize, usize)],
    ) -> bool {
        let loc = placed.len();
        // check upper tile which number is id - align
        if align <= loc {
            let (upper, r, f) = &placed[loc - align];
            if self.transpose(rotate, flip)[Dir::TOP.as_index()]
                != upper.transpose(*r, *f)[Dir::TOP.opposite()]
            {
                return false;
            }
        }
        if 0 < loc % align {
            let (left, r, f) = &placed[loc - 1];
            if self.transpose(rotate, flip)[Dir::LEFT.as_index()]
                != left.transpose(*r, *f)[Dir::LEFT.opposite()]
            {
                return false;
            }
        }
        true
    }
    /// ```
    /// use adventofcode::y2020::day20::*;
    /// assert_eq!(Tile::from(0, &vec!["...", "...", "..."]), Tile { id: 0, sign: [0, 0, 0,0 ], len: 3, image: vec!["...".to_string(), "...".to_string(), "...".to_string()] });
    /// ```
    pub fn from(id: usize, block: &[&str]) -> Self {
        let top = decode(&block[0].chars().collect::<Vec<char>>());
        let right = decode(
            &block
                .iter()
                .map(|l| l.chars().last().unwrap())
                .collect::<Vec<char>>(),
        );
        let bottom = decode(&block.last().unwrap().chars().collect::<Vec<char>>());
        let left = decode(
            &block
                .iter()
                .map(|l| l.chars().next().unwrap())
                .collect::<Vec<char>>(),
        );
        assert_eq!(block.len(), block[0].len());
        Tile {
            id,
            sign: [top, right, bottom, left],
            len: block.len(),
            image: block.iter().map(|s| s.to_string()).collect::<Vec<String>>(),
        }
    }
    //
    // part 2
    //
    pub fn new_empty_image(&self, with_border: bool) -> Vec<String> {
        let mut v: Vec<String> = Vec::new();
        if with_border {
            for _ in self.image.iter() {
                v.push(String::new())
            }
        } else {
            for _ in self.image.iter().take(self.len - 1).skip(1) {
                v.push(String::new())
            }
        }
        v
    }
    pub fn paste_image(&self, with_border: bool, rotate: usize, flip: usize, vec: &mut [String]) {
        let mut chars: Vec<char> = Vec::new();
        if with_border {
            assert_eq!(vec.len(), 10);
            for line in self.image.iter() {
                for c in line.chars() {
                    chars.push(c);
                }
            }
            assert_eq!(chars.len(), self.len * self.len);
        } else {
            assert_eq!(vec.len(), 8);
            for line in self.image.iter().take(self.len - 1).skip(1) {
                for c in line.chars().take(self.len - 1).skip(1) {
                    chars.push(c);
                }
            }
            assert_eq!(chars.len(), (self.len - 2) * (self.len - 2));
        }
        let at = |i0: usize, j0: usize| {
            let len = if with_border {
                self.len - 1
            } else {
                self.len - 3
            };
            let mut i = i0;
            let mut j = j0;
            if flip == 1 {
                j = len - j;
            }
            match rotate {
                1 => {
                    let ix = i;
                    i = len - j;
                    j = ix;
                }
                2 => {
                    i = len - i;
                    j = len - j;
                }
                3 => {
                    let ix = i;
                    i = j;
                    j = len - ix;
                }
                _ => (),
            }
            if with_border {
                chars[i * self.len + j]
            } else {
                chars[i * (self.len - 2) + j]
            }
        };
        for (i, line) in vec.iter_mut().enumerate() {
            if with_border {
                for j in 0..self.len {
                    line.push(at(i, j));
                }
            } else {
                for j in 0..self.len - 2 {
                    line.push(at(i, j));
                }
            }
        }
        //for (i, s) in self.image.iter().take(self.len - 1).skip(1).enumerate() {
        //    vec[i].push_str(&s[1..self.len - 1]);
        //}
    }
}

pub fn transose_image(image: &[String], rotate: usize, flip: usize) -> Vec<String> {
    let mut chars: Vec<char> = Vec::new();
    for line in image.iter() {
        for c in line.chars() {
            chars.push(c);
        }
    }
    let len = image.len();
    assert_eq!(chars.len(), len * len);
    let at = |i0: usize, j0: usize| {
        let len1 = len - 1;
        let mut i = i0;
        let mut j = j0;
        if flip == 1 {
            j = len1 - j;
        }
        match rotate {
            1 => {
                let ix = i;
                i = len1 - j;
                j = ix;
            }
            2 => {
                i = len1 - i;
                j = len1 - j;
            }
            3 => {
                let ix = i;
                i = j;
                j = len1 - ix;
            }
            _ => (),
        }
        chars[i * len + j]
    };
    let mut vec: Vec<String> = Vec::new();
    for i in 0..len {
        let mut line: String = String::new();
        for j in 0..len {
            line.push(at(i, j));
        }
        vec.push(line);
    }
    vec
}

/// ```
/// use adventofcode::y2020::day20::*;
/// assert_eq!(decode(&"....".chars().collect::<Vec<char>>()), 0);
/// assert_eq!(decode(&"...#".chars().collect::<Vec<char>>()), 1);
/// assert_eq!(decode(&"..##".chars().collect::<Vec<char>>()), 3);
/// ```
pub fn decode(line: &[char]) -> usize {
    line.iter()
        .fold(0, |acum, c| acum * 2 + ((*c == '#') as usize))
}

fn count_sharps(vec: &[String]) -> usize {
    vec.iter()
        .map(|line| line.chars().filter(|c| *c == '#').count())
        .sum()
}

fn check_sea_monstar(image: &[String]) -> usize {
    lazy_static! {
        static ref MONSTER_HEAD: Regex = Regex::new(r"^..................#.").expect("error");
        static ref MONSTER_BODY: Regex = Regex::new(r"^#....##....##....###").expect("error");
        static ref MONSTER_DOWN: Regex = Regex::new(r"^.#..#..#..#..#..#...").expect("error");
    }
    let mut count = 0;
    let len = image.len();
    for (i, line) in image.iter().enumerate().take(len - 1).skip(1) {
        for j in 0..line.len() {
            if MONSTER_BODY.captures(&line[j..]).is_some()
                && MONSTER_HEAD.captures(&image[i - 1][j..]).is_some()
                && MONSTER_DOWN.captures(&image[i + 1][j..]).is_some()
            {
                count += 1;
            }
        }
    }
    count
}

fn eval(tile: &[Tile]) -> Option<Vec<(Tile, usize, usize)>> {
    let len = (tile.len() as f64).sqrt() as usize;
    let used: Vec<(Tile, usize, usize)> = Vec::new();
    let remain = tile.to_vec();
    println!("#tiles: {}", tile.len());
    search(len, used, remain)
}

fn search(
    align: usize,
    used: Vec<(Tile, usize, usize)>,
    remain: Vec<Tile>,
) -> Option<Vec<(Tile, usize, usize)>> {
    if remain.is_empty() {
        return Some(used);
    }
    for tile in remain.iter() {
        for rotate in 0..4 {
            for flip in 0..2 {
                if tile.valid(align, rotate, flip, &used) {
                    let mut u = used.clone();
                    u.push((tile.clone(), rotate, flip));
                    let mut r = remain.clone();
                    r.retain(|t| t != tile);
                    /* for _ in 0..u.len() - 1 {
                        print!(" ");
                    }
                    println!("assume {}", tile.id); */
                    if let Some(ans) = search(align, u, r) {
                        return Some(ans);
                    }
                }
            }
        }
    }
    None
}

#[cfg(feature = "y2020")]
#[cfg(test)]
mod test {
    use {
        super::*,
        crate::y2020::traits::{Answer, Description},
    };

    #[test]
    fn test_basic_computations() {
        assert_eq!(usize::from_str_radix("0010111000", 2), Ok(184));
        assert_eq!(usize::from_str_radix("0101011100", 2), Ok(348));
        assert_eq!(
            flip_bits(10, 348),
            usize::from_str_radix("0011101010", 2).unwrap()
        );
        assert_eq!(flip_bits(10, 348), 234);
        assert_eq!(usize::from_str_radix("0111110010", 2), Ok(498));
        assert_eq!(decode(&"0#####00#0".chars().collect::<Vec<char>>()), 498);
        assert_eq!(usize::from_str_radix("0100111110", 2), Ok(318));
    }

    #[test]
    fn test_part1() {
        assert_eq!(
            Setting::parse(Description::FileTag("test1".to_string())).run(1),
            Answer::Part1(20899048083289)
        );
    }

    #[test]
    fn test_part2() {
        assert_eq!(
            Setting::parse(Description::FileTag("test1".to_string())).run(2),
            Answer::Part2(273)
        );
    }
}
