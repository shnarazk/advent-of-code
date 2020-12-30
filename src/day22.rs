use {
    crate::{Description, ProblemSolver},
    lazy_static::lazy_static,
    regex::Regex,
    std::{
        cmp::Ordering,
        collections::{HashSet, VecDeque},
    },
};

pub fn day22(part: usize, desc: Description) {
    dbg!(World::parse(desc).run(part));
}

fn parse(block: &str) -> Option<VecDeque<usize>> {
    lazy_static! {
        static ref HEAD: Regex = Regex::new(r"^Player (\d+):").expect("error");
    }
    if HEAD.captures(block).is_some() {
        let mut q: VecDeque<usize> = VecDeque::new();
        for l in block.split('\n').skip(1) {
            if l.is_empty() {
                break;
            }
            q.push_back(l.parse::<usize>().expect("panic"));
        }
        return Some(q);
    }
    None
}

type Player = VecDeque<usize>;
type Config = (Player, Player);

#[derive(Debug, PartialEq)]
struct Cache {
    set: HashSet<Config>,
}

impl Cache {
    fn new() -> Cache {
        Cache {
            set: HashSet::new(),
        }
    }
    fn saw(&mut self, player1: &Player, player2: &Player) -> Option<usize> {
        if self.set.contains(&(player1.clone(), player2.clone())) {
            return Some(1);
        }
        if self.set.contains(&(player2.clone(), player1.clone())) {
            return Some(2);
        }
        let len = self.set.len();
        self.set.insert((player1.clone(), player2.clone()));
        debug_assert!(self.set.contains(&(player1.clone(), player2.clone())));
        debug_assert_eq!(len + 1, self.set.len());
        None
    }
}

#[derive(Debug, PartialEq)]
struct World {
    player1: Player,
    player2: Player,
    cache: Cache,
}

impl ProblemSolver<(), usize, usize> for World {
    const DAY: usize = 22;
    const DELIMITER: &'static str = "\n\n";
    fn default() -> Self {
        World {
            player1: VecDeque::new(),
            player2: VecDeque::new(),
            cache: Cache::new(),
        }
    }
    fn parse(desc: Description) -> Self {
        let mut instance = Self::default();
        if let Some(buffer) = Self::load(desc) {
            let mut iter = buffer.split(Self::DELIMITER);
            if let Some(text) = iter.next() {
                if let Some(element) = parse(text) {
                    instance.player1 = element;
                }
            }
            if let Some(text) = iter.next() {
                if let Some(element) = parse(text) {
                    instance.player2 = element;
                }
            }
        }
        instance
    }
    fn part1(&mut self) -> usize {
        let mut stopper = None;
        while self.check_winner(stopper).is_none() {
            stopper = self.round_part1();
            println!(
                " 1 -> {:?}\n 2 -> {:?}\n {} cached, stopper: {:?}",
                &self.player1,
                &self.player2,
                self.cache.set.len(),
                stopper
            );
        }
        let mut score = 0;
        if let Some(p) = self.check_winner(stopper) {
            println!(
                "found winner {}: {:?} {:?}",
                p, &self.player1, &self.player2
            );
            let v = if p == 1 { &self.player1 } else { &self.player2 };
            for (i, h) in v.iter().rev().enumerate() {
                score += (i + 1) * *h;
                // println!("{} * {} = {} => {}, ", *h, i + 1, (i + 1) * *h, score);
            }
        }
        score
    }
    fn part2(&mut self) -> usize {
        let mut stopper = None;
        while self.check_winner(stopper).is_none() {
            stopper = self.round_part2();
        }
        let mut score = 0;
        if let Some(p) = self.check_winner(stopper) {
            println!(
                "found winner {}: {:?} {:?}",
                p, &self.player1, &self.player2
            );
            let v = if p == 1 { &self.player1 } else { &self.player2 };
            for (i, h) in v.iter().rev().enumerate() {
                score += (i + 1) * *h;
            }
        }
        score
    }
}

impl World {
    fn check_winner(&self, exception: Option<usize>) -> Option<usize> {
        if exception.is_some() {
            return exception;
        }
        if self.player2.is_empty() {
            return Some(1);
        } else if self.player1.is_empty() {
            return Some(2);
        }
        None
    }
    fn round_part1(&mut self) -> Option<usize> {
        if let Some(h1) = self.player1.pop_front() {
            if let Some(h2) = self.player2.pop_front() {
                match h1.cmp(&h2) {
                    Ordering::Less => {
                        self.player2.push_back(h2);
                        self.player2.push_back(h1);
                        // println!("Player2 won with {} against {}", h2, h1);
                    }
                    Ordering::Equal => panic!("equals!"),
                    Ordering::Greater => {
                        self.player1.push_back(h1);
                        self.player1.push_back(h2);
                        // println!("Player1 won with {} against {}", h1, h2);
                    }
                }
                // println!("Player1: {:?}", self.player1);
                // println!("Player2: {:?}", self.player2);
                None
            } else {
                self.player1.push_front(h1);
                Some(1)
            }
        } else {
            Some(2)
        }
    }
    fn round_part2(&mut self) -> Option<usize> {
        if self.player1.is_empty() {
            return Some(2);
        }
        if self.player2.is_empty() {
            return Some(1);
        }
        if let Some(x) = self.cache.saw(&self.player1, &self.player2) {
            return Some(x);
        }
        if let Some(p1_head) = self.player1.pop_front() {
            if let Some(p2_head) = self.player2.pop_front() {
                let append_to_p1: bool = {
                    if p1_head <= self.player1.len() && p2_head <= self.player2.len() {
                        let mut child = World::default();
                        child.player1 = self.player1.clone();
                        child.player2 = self.player2.clone();
                        child.player1.truncate(p1_head);
                        child.player2.truncate(p2_head);
                        println!(
                            "{:>width$}",
                            ">",
                            width = child.player1.len() + child.player2.len()
                        );
                        let mut stopper = None;
                        while child.check_winner(stopper).is_none() {
                            stopper = child.round_part2();
                        }
                        child.check_winner(stopper).expect("impossible") == 1
                    } else {
                        p2_head < p1_head
                    }
                };
                if append_to_p1 {
                    self.player1.push_back(p1_head);
                    self.player1.push_back(p2_head);
                } else {
                    self.player2.push_back(p2_head);
                    self.player2.push_back(p1_head);
                }
            }
        }
        None
    }
}

#[cfg(test)]
mod test {
    use {
        super::*,
        crate::{Answer, Description},
    };
    #[test]
    fn test0() {
        const TEST: &str = "\
Player 1:
3
1

Player 2:
7
10";
        assert_eq!(
            World::parse(Description::TestData(TEST.to_string())).run(1),
            Answer::Part1(58)
        );
    }
    #[test]
    fn test_loop() {
        const TEST: &str = "\
Player 1:
43
19

Player 2:
2
29
14";
        assert_eq!(
            World::parse(Description::TestData(TEST.to_string())).run(2),
            Answer::Part2(43 * 2 + 19 * 1)
        );
    }
    #[test]
    fn test1() {
        const TEST: &str = "\
Player 1:
9
2
6
3
1

Player 2:
5
8
4
7
10";
        assert_eq!(
            World::parse(Description::TestData(TEST.to_string())).run(2),
            Answer::Part2(291)
        );
    }
    #[test]
    fn test2() {
        const TEST: &str = "\
Player 1:
9
2
6
3

Player 2:
1";
        assert_eq!(
            World::parse(Description::TestData(TEST.to_string())).run(1),
            Answer::Part1(2 * 5 + 6 * 4 + 3 * 3 + 9 * 2 + 1 * 1)
        );
    }
}
