#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    lazy_static::lazy_static,
    regex::Regex,
    std::{
        collections::{HashMap, HashSet, VecDeque},
        io::{stdin, Read},
    },
};

fn main() {
    let mut buf = String::new();
    stdin().read_to_string(&mut buf).expect("wrong");
    read(&buf.trim());
}

fn parse(block: &str) -> Option<VecDeque<usize>> {
    lazy_static! {
        static ref HEAD: Regex = Regex::new(r"^Player (\d+):").expect("error");
    }
    if let Some(m) = HEAD.captures(block) {
        let mut q: VecDeque<usize> = VecDeque::new();
        for l in block.split('\n').skip(1) {
            q.push_back(l.parse::<usize>().expect("panic"));
        }
        return Some(q);
    }
    None
}

type Player = VecDeque<usize>;
type Config = (Player, Player);
struct Cache {
    set: HashSet<Config>,
}

impl Cache {
    fn new() -> Cache {
        Cache {
            set: HashSet::new(),
        }
    }
    fn saw(&mut self, player1: &mut Player, player2: &mut Player) -> Option<usize> {
        let len = self.set.len();
        if self.set.contains(&(player1.clone(), player2.clone())) {
            return Some(1);
        }
        self.set.insert((player1.clone(), player2.clone()));
        debug_assert!(self.set.contains(&(player1.clone(), player2.clone())));
        debug_assert_eq!(len + 1, self.set.len());
        None
    }
}
struct GameCache {
    limit: usize,
    cache: HashMap<Config, bool>,
}

impl GameCache {
    fn new() -> GameCache {
        GameCache {
            limit: 42,
            cache: HashMap::new(),
        }
    }
    fn contains(&mut self, player1: &Player, player2: &Player) -> Option<&bool> {
        let result = self.cache.get(&(player1.clone(), player2.clone()));
        if result.is_some() {
            return result;
        }
        // a same length pair can check after rotations.
        if player1.len() == player2.len() {
            for i in 1..player1.len() {}
            
            }
        }
        None
    }
    fn insert(&mut self, player1: &Player, player2: &Player, val: bool) -> bool {
        if player1.len() + player2.len() < self.limit {
            *self.cache.entry((player1.clone(), player2.clone())).or_insert(false) = val;
            // if self.cache.len() % 10000 == 0 {
            //     println!("{}", self.cache.len());
            // }
            val
        } else {
            val
        }
    }
}

fn read(buf: &str) -> usize {
    // let mut dic;
    let mut players: Vec<Player> = Vec::new();
    for block in buf.split("\n\n") {
        // dbg!(&block);
        if let Some(p) = parse(block) {
            players.push(p);
        }
    }
    // dbg!(&players);
    let mut p1 = players[0].clone();
    let mut p2 = players[1].clone();
    // let mut checker: HashSet<Config> = HashSet::new();
    // let mut cache: HashSet<Config> = HashSet::new();
    let mut cache = Cache::new();
    let mut game_cache = GameCache::new();
    let mut stopper = None;
    println!(" 1 -> {:?}\n 2 -> {:?}", &p1, &p2);
    while winner(stopper, &p1, &p2).is_none() {
        stopper = run2(&mut p1, &mut p2, &mut cache, &mut game_cache);
        println!(" 1 -> {:?}\n 2 -> {:?}\n {} cached, stopper: {:?}", &p1, &p2, cache.set.len(), stopper);
    }
    let mut score = 0;
    if let Some(p) = winner(stopper, &p1, &p2) {
        println!("found winner {}: {:?} {:?}", p, &p1, &p2);
        let v = if p == 1 { p1 } else { p2 };
        for (i, h) in v.iter().rev().enumerate() {
            score += (i + 1) * *h;
            // println!("{} * {} = {} => {}, ", *h, i + 1, (i + 1) * *h, score);
        }
    }
    dbg!(score);
    score
}

// part 1
fn run1(player1: &mut Player, player2: &mut Player) -> Option<usize> {
    if let Some(h1) = player1.pop_front() {
        if let Some(h2) = player2.pop_front() {
            if h1 < h2 {
                player2.push_back(h2);
                player2.push_back(h1);
                println!("Player2 won with {} against {}", h2, h1);
                println!("Player1: {:?}", player1);
                println!("Player2: {:?}", player2);
                // dbg!(&player2);
            } else if h2 < h1 {
                player1.push_back(h1);
                player1.push_back(h2);
                println!("Player1 won with {} against {}", h1, h2);
                println!("Player1: {:?}", player1);
                println!("Player2: {:?}", player2);
                // dbg!(&player1);
            } else {
                panic!("equals!");
            }
            None
        } else {
            player1.push_front(h1);
            Some(1)
        }
    } else {
        Some(2)
    }
}

fn run2(player1: &mut Player, player2: &mut Player, cache: &mut Cache, game_cache: &mut GameCache) -> Option<usize> {
    if player1.is_empty() {
        return Some(2);
    }
    if  player2.is_empty() {
        return Some(1);
    }
    if let Some(x) = cache.saw(player1, player2) {
        return Some(x);
    }
    if let Some(p1_head) = player1.pop_front() {
        if let Some(p2_head) = player2.pop_front() {
            let append_to_p1: bool = {
                if p1_head <= player1.len() && p2_head <= player2.len() {
                    let mut p1 = player1.clone();
                    let mut p2 = player2.clone();
                    if let Some(result) = game_cache.contains(&p1, &p2) {
                        *result
                    } else {
                        let mut new_cache = Cache::new();
                        let mut stopper = None;
                        while winner(stopper, &p1, &p2).is_none() {
                            stopper = run2(&mut p1, &mut p2, &mut new_cache, game_cache);
                        }
                        match winner(stopper, &p1, &p2) {
                            Some(n) => {
                                game_cache.insert(&p1, &p2, n == 1)
                            },
                            None => panic!("eeae")
                        }
                    }
                } else {
                    p2_head < p1_head
                }
            };
            if append_to_p1 {
                player1.push_back(p1_head);
                player1.push_back(p2_head);
            } else {
                player2.push_back(p2_head);
                player2.push_back(p1_head);
            }
        }
    }
    None
}

fn winner(exception: Option<usize>, p1: &Player, p2: &Player) -> Option<usize> {
    if exception.is_some() {
        return exception
    }
    if p2.is_empty() {
        return Some(1);
    } else if p1.is_empty() {
        return Some(2);
    }
    None
}

mod test {
    use super::*;
    #[test]
    fn test0() {
        const TEST: &str = "\
Player 1:
3
1

Player 2:
7
10";
        assert_eq!(read(TEST), 58);
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
        assert_eq!(read(TEST), 43 * 2 + 19 * 1);
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
        assert_eq!(read(TEST), 291);
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
        assert_eq!(read(TEST), 2 * 5 + 6 * 4 + 3 * 3 + 9 * 2 + 1 * 1);
    }
}
