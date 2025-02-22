//! <https://adventofcode.com/2021/day/18>
use {
    crate::{
        color,
        framework::{AdventOfCode, ParseError, aoc},
    },
    std::fmt,
};

#[derive(Clone, PartialEq)]
pub enum Tree {
    Num(usize),
    List(Vec<Tree>),
}

impl fmt::Debug for Tree {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fn leveled(t: &Tree, level: usize) -> String {
            match t {
                Tree::Num(n) => {
                    if 9 < *n {
                        if 4 < level {
                            format!("{}{}{}", color::GREEN, n, color::RED)
                        } else {
                            format!("{}{}{}", color::GREEN, n, color::RESET)
                        }
                    } else {
                        format!("{}", n)
                    }
                }
                Tree::List(v) => {
                    let str = format!(
                        "[{}]",
                        v.iter()
                            .map(|n| leveled(n, level + 1))
                            .collect::<Vec<_>>()
                            .join(",")
                    );
                    if 4 == level {
                        format!("{}{}{}", color::RED, str, color::RESET)
                    } else {
                        str
                    }
                }
            }
        }
        match self {
            Tree::Num(n) => write!(f, "{}", n),
            Tree::List(_) => write!(f, "{}", leveled(self, 0)),
        }
    }
}

impl Tree {
    pub fn from_str_(str: &str) -> Tree {
        if let Tree::List(node) =
            Tree::from(&str.chars().filter(|c| *c != ',').collect::<Vec<char>>()).0
        {
            return node[0].clone();
        }
        panic!();
    }
    fn from(mut str: &[char]) -> (Tree, &[char]) {
        let mut tree: Vec<Tree> = Vec::new();
        while !str.is_empty() {
            match str[0] {
                d if d.is_ascii_digit() => {
                    tree.push(Tree::Num(str[0] as usize - '0' as usize));
                    str = &str[1..];
                }
                '[' => {
                    let (node, next) = Tree::from(&str[1..]);
                    tree.push(node);
                    str = next;
                }
                ']' => {
                    return (Tree::List(tree), &str[1..]);
                }
                _ => panic!("{:?}", str),
            }
        }
        debug_assert!(!tree.is_empty());
        (Tree::List(tree), str)
    }
    fn size(&self) -> usize {
        match self {
            Tree::Num(_) => 1,
            Tree::List(v) => v.iter().map(|n| n.size()).sum(),
        }
    }
    fn increment_at(mut self, mut pos: usize, val: usize) -> Self {
        match self {
            Tree::Num(ref mut n) if pos == 0 => *n += val,
            Tree::List(ref mut v) => {
                for n in v.iter_mut() {
                    let s = n.size();
                    if pos < s {
                        *n = n.clone().increment_at(pos, val);
                        break;
                    }
                    pos -= s;
                }
            }
            _ => (),
        }
        self
    }
    fn splits(&mut self) -> (Self, bool) {
        fn go_down(tree: &Tree) -> (Tree, bool) {
            match tree {
                Tree::Num(n) if 9 < *n => (
                    Tree::List(vec![Tree::Num(n / 2), Tree::Num((n + 1) / 2)]),
                    true,
                ),
                Tree::List(v) => {
                    let mut new_vec = v.clone();
                    for (i, n) in v.iter().enumerate() {
                        let (nn, found) = go_down(n);
                        if found {
                            new_vec[i] = nn;
                            return (Tree::List(new_vec), true);
                        }
                    }
                    (tree.clone(), false)
                }
                _ => (tree.clone(), false),
            }
        }
        go_down(self)
    }
    fn explode(&mut self) -> (Self, bool) {
        fn go_down(
            tree: Tree,
            level: usize,
            mut start: usize,
        ) -> (Tree, usize, Option<(usize, usize)>) {
            match tree {
                Tree::List(v) => {
                    let mut new_vec: Vec<Tree> = v.clone();
                    // println!(" - level{} {:?}", level, &new_vec);
                    if 4 <= level
                        && v.len() == 2
                        && matches!(v[0], Tree::Num(_))
                        && matches!(v[1], Tree::Num(_))
                    {
                        match (&v[0], &v[1]) {
                            (Tree::Num(a1), Tree::Num(a2)) => {
                                // println!(" - explode {:?} at {}", &new_vec, start);
                                return (Tree::Num(0), start, Some((*a1, *a2)));
                            }
                            _ => unreachable!(),
                        }
                    } else {
                        for i in 0..v.len() {
                            let (t, n, f) = go_down(new_vec[i].clone(), level + 1, start);
                            new_vec[i] = t;
                            start = n;
                            if f.is_some() {
                                return (Tree::List(new_vec), start, f);
                            }
                        }
                    }
                    (Tree::List(new_vec), start, None)
                }
                Tree::Num(_) => (tree, start + 1, None),
            }
        }
        let (t, n, f) = go_down(self.clone(), 0, 0);
        if let Some(k) = f {
            let mut tree = t;
            // println!(" {} {:?}", n, &tree);
            if 0 < n {
                tree = tree.increment_at(n - 1, k.0);
                // println!(" ({},{})< {:?}", n - 1, k.0, &tree);
            }
            if n < tree.size() {
                tree = tree.increment_at(n + 1, k.1);
                // println!(" ({},{})> {:?}", n + 1, k.1, &tree);
            }
            (tree, true)
        } else {
            (t, false)
        }
    }
    fn add(&self, tree: &Tree) -> Tree {
        Tree::List(vec![self.clone(), tree.clone()])
    }
    fn magnitude(&self) -> usize {
        match self {
            Tree::List(v) => 3 * v[0].magnitude() + 2 * v[1].magnitude(),
            Tree::Num(n) => *n,
        }
    }
}

#[derive(Clone, Debug, Default)]
pub struct Puzzle {
    line: Vec<Tree>,
}

#[aoc(2021, 18)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, input: &str) -> Result<(), ParseError> {
        for block in input.lines() {
            let str = &block.chars().filter(|c| *c != ',').collect::<Vec<_>>();
            let (node, _rest) = Tree::from(str);
            if let Tree::List(mut v) = node {
                if let Some(node) = v.pop() {
                    self.line.push(node);
                }
            }
        }
        Self::parsed()
    }
    fn part1(&mut self) -> Self::Output1 {
        self.line.reverse();
        let mut transformed = self.line.pop().unwrap(); // l.clone().explode();
        self.line.reverse();
        for l in self.line.iter() {
            // println!("\n+ {:?}", &l);
            transformed = transformed.add(l);
            // println!("\tafter addition: {:?}", &transformed);
            let mut modified = true;
            while modified {
                if modified {
                    let (n, m) = transformed.explode();
                    transformed = n;
                    modified = m;
                }
                if modified {
                    // println!("\tafter explode:  {:?}", &transformed);
                    continue;
                }
                let mut spliting = true;
                if spliting {
                    let (n, m) = transformed.splits();
                    transformed = n;
                    spliting = m;
                    if spliting {
                        modified = true;
                    }
                }
                // if modified {
                //     println!("\tafter split:    {:?}", &transformed);
                // }
            }
            // println!("= {:?}", &transformed);
        }
        transformed.magnitude()
    }
    fn part2(&mut self) -> Self::Output2 {
        fn add(n1: &Tree, n2: &Tree) -> usize {
            let mut transformed = n1.add(n2);
            // println!("\tafter addition: {:?}", &transformed);
            let mut modified = true;
            while modified {
                if modified {
                    let (n, m) = transformed.explode();
                    transformed = n;
                    modified = m;
                }
                if modified {
                    // println!("\tafter explode:  {:?}", &transformed);
                    continue;
                }
                let mut spliting = true;
                if spliting {
                    let (n, m) = transformed.splits();
                    transformed = n;
                    spliting = m;
                    if spliting {
                        modified = true;
                    }
                }
                if modified {
                    // println!("\tafter split:    {:?}", &transformed);
                }
            }
            // println!("= {:?}", &transformed);
            transformed.magnitude()
        }
        let mut max_num = 0;
        let len = self.line.len();
        for j in 0..len {
            for i in 0..len {
                if i == j {
                    continue;
                }
                let x = add(&self.line[j], &self.line[i]);
                if max_num < x {
                    max_num = x;
                }
            }
        }
        max_num
    }
}

#[cfg(feature = "y2021")]
#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_part1() {
        assert_eq!(
            Tree::from_str_("[[[[[9,8],1],2],3],4]").explode().0,
            Tree::from_str_("[[[[0,9],2],3],4]")
        );
        assert_eq!(
            Tree::from_str_("[7,[6,[5,[4,[3,2]]]]]").explode().0,
            Tree::from_str_("[7,[6,[5,[7,0]]]]")
        );
        assert_eq!(
            Tree::from_str_("[[6,[5,[4,[3,2]]]],1]").explode().0,
            Tree::from_str_("[[6,[5,[7,0]]],3]")
        );
        assert_eq!(
            Tree::from_str_("[[3,[2,[1,[7,3]]]],[6,[5,[4,[3,2]]]]]")
                .explode()
                .0,
            Tree::from_str_("[[3,[2,[8,0]]],[9,[5,[4,[3,2]]]]]")
        );
        assert_eq!(
            Tree::from_str_("[[3,[2,[8,0]]],[9,[5,[4,[3,2]]]]]")
                .explode()
                .0,
            Tree::from_str_("[[3,[2,[8,0]]],[9,[5,[7,0]]]]")
        );
    }
    #[test]
    fn test_magnitude() {
        assert_eq!(Tree::from_str_("[9,1]").magnitude(), 29);
        assert_eq!(Tree::from_str_("[1,9]").magnitude(), 21);
        assert_eq!(Tree::from_str_("[[9,1],[1,9]]").magnitude(), 129);
        assert_eq!(Tree::from_str_("[[1,2],[[3,4],5]]").magnitude(), 143);
        assert_eq!(
            Tree::from_str_("[[[[0,7],4],[[7,8],[6,0]]],[8,1]]").magnitude(),
            1384
        );
        assert_eq!(
            Tree::from_str_("[[[[1,1],[2,2]],[3,3]],[4,4]]").magnitude(),
            445
        );
        assert_eq!(
            Tree::from_str_("[[[[3,0],[5,3]],[4,4]],[5,5]]").magnitude(),
            791
        );
        assert_eq!(
            Tree::from_str_("[[[[5,0],[7,4]],[5,5]],[6,6]]").magnitude(),
            1137
        );
        assert_eq!(
            Tree::from_str_("[[[[8,7],[7,7]],[[8,6],[7,7]]],[[[0,7],[6,6]],[8,7]]]").magnitude(),
            3488
        );
    }
}
