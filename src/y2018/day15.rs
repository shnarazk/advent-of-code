//! <https://adventofcode.com/2018/day/15>
use {
    crate::framework::{AdventOfCode, ParseError, aoc},
    core::cmp::Reverse,
    std::collections::{BinaryHeap, HashMap, HashSet},
};

const HIT_POINT: usize = 200;
const ATTACK_POWER: usize = 3;

type Dim2 = (isize, isize);

/// direction vectors in reading order
const DIRS: [Dim2; 4] = [(-1, 0), (0, -1), (0, 1), (1, 0)];

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
enum Creature {
    Elf(Dim2, usize, usize),
    Goblin(Dim2, usize, usize),
}

impl PartialOrd for Creature {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Creature {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.position().cmp(other.position())
    }
}

impl Creature {
    fn is_elf(&self) -> bool {
        matches!(self, Creature::Elf(_, _, _))
    }
    fn id(&self) -> usize {
        match self {
            Creature::Elf(_, _, id) => *id,
            Creature::Goblin(_, _, id) => *id,
        }
    }
    fn hit_point(&self) -> usize {
        match self {
            Creature::Elf(_, hp, _) => *hp,
            Creature::Goblin(_, hp, _) => *hp,
        }
    }
    fn decrement_hit_point(&mut self, power: usize) -> bool {
        let p = match self {
            Creature::Elf(_, hp, _) => hp,
            Creature::Goblin(_, hp, _) => hp,
        };
        *p = p.saturating_sub(power);
        *p == 0
    }
    fn position(&self) -> &Dim2 {
        match self {
            Creature::Elf(p, _, _) => p,
            Creature::Goblin(p, _, _) => p,
        }
    }
    fn set_position(&mut self, to: &Dim2) {
        match self {
            Creature::Elf(p, _, _) => {
                p.0 = to.0;
                p.1 = to.1;
            }
            Creature::Goblin(p, _, _) => {
                p.0 = to.0;
                p.1 = to.1;
            }
        }
    }
    fn target_creatures<'b>(&self, world: &'b Puzzle) -> Vec<&'b Creature> {
        world
            .creatures
            .iter()
            .filter(|c| self.is_elf() != c.is_elf())
            .collect::<Vec<_>>()
    }
    fn all_ranges(&self, world: &Puzzle) -> Vec<Dim2> {
        let v = self.target_creatures(world);
        let mut valids: HashSet<Dim2> = HashSet::new();
        for c in v.iter() {
            let p = c.position();
            for adj in DIRS {
                let q = (p.0 + adj.0, p.1 + adj.1);
                if world.map.contains(&q) && world.creatures.iter().all(|c| *c.position() != q) {
                    valids.insert(q);
                }
            }
        }
        valids.iter().copied().collect::<Vec<Dim2>>()
    }
    fn best_moving_position(&self, world: &Puzzle) -> Option<Dim2> {
        let pos = self.position();
        let v = self.all_ranges(world);
        // {
        //     let mut h: HashMap<Dim2, char> = HashMap::new();
        //     for p in v.iter() {
        //         h.insert(*p, '?');
        //     }
        //     world.render(Some(h));
        // }
        let table = world.build_distance_table(*pos);
        let mut targets = Vec::new();
        let mut dist_min = usize::MAX;
        for p in v.iter() {
            if let Some(d) = table.get(p) {
                match d.cmp(&dist_min) {
                    std::cmp::Ordering::Equal => targets.push(p),
                    std::cmp::Ordering::Less => {
                        targets.clear();
                        targets.push(p);
                        dist_min = *d;
                    }
                    std::cmp::Ordering::Greater => (),
                }
            }
        }
        (!targets.is_empty()).then(|| {
            targets.sort();
            *targets[0]
        })
    }
    fn is_in_a_range<'b>(&self, world: &'b Puzzle) -> Option<Vec<&'b Creature>> {
        let p = self.position();
        let enemies = self.target_creatures(world);
        let mut targets: HashSet<&Creature> = HashSet::new();
        for adj in DIRS {
            let q = (p.0 + adj.0, p.1 + adj.1);
            for e in enemies.iter() {
                if *e.position() == q {
                    targets.insert(*e);
                }
            }
        }
        (!targets.is_empty()).then(|| targets.iter().copied().collect::<Vec<_>>())
    }
    // return `true `if I attacked.
    fn attack(&mut self, world: &mut Puzzle) -> bool {
        let mut targets = Vec::new();
        if let Some(v) = self.is_in_a_range(world) {
            let mut hp = usize::MAX;
            for enemy in v.iter() {
                let h = enemy.hit_point();
                match h.cmp(&hp) {
                    std::cmp::Ordering::Less => {
                        targets.clear();
                        targets.push(enemy.position());
                        hp = h;
                    }
                    std::cmp::Ordering::Equal => {
                        targets.push(enemy.position());
                    }
                    std::cmp::Ordering::Greater => (),
                }
            }
        }
        if targets.is_empty() {
            return false;
        }
        targets.sort();
        let target = *targets[0];
        if world.reduce_hp(&target) {
            world.kill_creature(&target);
        }
        true
    }
    fn exists_on(&self, world: &Puzzle) -> bool {
        let id = self.id();
        world.creatures.iter().any(|c| c.id() == id)
    }
    fn turn(&mut self, world: &mut Puzzle) -> bool {
        debug_assert!(self.exists_on(world));
        if self.attack(world) {
            return true;
        }
        let pos = self.position();
        if let Some(target) = self.best_moving_position(world) {
            let table = world.build_distance_table(target);
            // let h = table
            //     .iter()
            //     .filter(|(_, v)| **v < 10)
            //     .map(|(k, v)| (*k, (*v as u8 + b'0') as char))
            //     .collect::<HashMap<Dim2, _>>();
            // world.render(Some(h));
            let mut dist_so_far = usize::MAX;
            let mut r = *pos;
            for ad in DIRS.iter() {
                let q = (pos.0 + ad.0, pos.1 + ad.1);
                if let Some(d) = table.get(&q) {
                    if *d < dist_so_far {
                        dist_so_far = *d;
                        r = q;
                    }
                }
            }
            debug_assert_ne!(r, *pos);
            // println!(" - creatue at {:?} moves to {:?}", pos, r);
            world.move_creature(pos, &r);
            self.set_position(&r);
        }
        self.attack(world)
    }
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Puzzle {
    line: Vec<Vec<u8>>,
    map: HashSet<Dim2>,
    creatures: Vec<Creature>,
    height: usize,
    width: usize,
    elf_power: usize,
}

impl Puzzle {
    #[allow(dead_code)]
    fn render(&self, overlay: Option<HashMap<Dim2, char>>) {
        let mut map: HashMap<Dim2, char> = HashMap::new();
        let mut hps: HashMap<Dim2, usize> = HashMap::new();
        for c in self.creatures.iter() {
            map.insert(*c.position(), if c.is_elf() { 'E' } else { 'G' });
            hps.insert(*c.position(), c.hit_point());
        }
        if let Some(h) = overlay {
            for (k, v) in h.iter() {
                map.insert(*k, *v);
            }
        }
        for (j, l) in self.line.iter().enumerate() {
            let mut v: Vec<usize> = Vec::new();
            for (i, c) in l.iter().enumerate() {
                if let Some(hp) = hps.get(&(j as isize, i as isize)) {
                    v.push(*hp);
                }
                print!(
                    "{}",
                    map.get(&(j as isize, i as isize)).unwrap_or(&(*c as char))
                );
            }
            if v.is_empty() {
                println!();
            } else {
                println!(" {:?}", v);
            }
        }
    }
    fn build_distance_table(&self, from: Dim2) -> HashMap<Dim2, usize> {
        let mut to_visit: BinaryHeap<Reverse<(usize, Dim2)>> = BinaryHeap::new();
        let mut man: HashMap<Dim2, usize> = HashMap::new();
        let creatures: HashSet<Dim2> = self
            .creatures
            .iter()
            .map(|c| *c.position())
            .collect::<HashSet<_>>();
        to_visit.push(Reverse((0, from)));
        while let Some(Reverse((dist, pos))) = to_visit.pop() {
            if man.contains_key(&pos) {
                continue;
            }
            man.insert(pos, dist);
            for d in DIRS.iter() {
                let x = (pos.0 + d.0, pos.1 + d.1);
                if self.map.contains(&x) && !man.contains_key(&x) && !creatures.contains(&x) {
                    to_visit.push(Reverse((dist + 1, x)));
                }
            }
        }
        man
    }
    fn move_creature(&mut self, from: &Dim2, to: &Dim2) {
        for c in self.creatures.iter_mut() {
            if c.position() == from {
                c.set_position(to);
                break;
            }
        }
    }
    fn reduce_hp(&mut self, at: &Dim2) -> bool {
        for c in self.creatures.iter_mut() {
            if c.position() == at {
                let damage = if c.is_elf() {
                    ATTACK_POWER
                } else {
                    self.elf_power
                };
                return c.decrement_hit_point(damage);
            }
        }
        unreachable!()
    }
    fn kill_creature(&mut self, at: &Dim2) {
        self.creatures.retain(|c| c.position() != at)
    }
}

#[aoc(2018, 15)]
impl AdventOfCode for Puzzle {
    fn prepare(&mut self, input: &str) -> Result<(), ParseError> {
        self.line = input.lines().map(|line| line.as_bytes().to_vec()).collect();
        let mut count = 1;
        for (j, l) in self.line.iter_mut().enumerate() {
            for (i, c) in l.iter_mut().enumerate() {
                let pos = (j as isize, i as isize);
                if *c != b'#' {
                    self.map.insert(pos);
                }
                match *c {
                    b'E' => {
                        self.creatures.push(Creature::Elf(pos, HIT_POINT, count));
                        *c = b'.';
                        count += 1;
                    }
                    b'G' => {
                        self.creatures.push(Creature::Goblin(pos, HIT_POINT, count));
                        *c = b'.';
                        count += 1;
                    }
                    _ => (),
                }
            }
        }
        self.height = self.line.len();
        self.width = self.line[0].len();
        self.elf_power = ATTACK_POWER;
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        // self.render(None);
        for turn in 0.. {
            self.creatures.sort();
            let mut creatures = self.creatures.clone();
            for c in creatures.iter_mut() {
                if !c.exists_on(self) {
                    continue;
                }
                if c.target_creatures(self).is_empty() {
                    // println!("On turn {}, ", turn + 1);
                    // self.render(None);
                    debug_assert!(self.creatures.iter().all(|c| 0 < c.hit_point()));
                    let hit_points = self.creatures.iter().map(|c| c.hit_point()).sum::<usize>();
                    return turn * hit_points;
                }
                c.turn(self);
            }
            // println!("turn {} completed.", turn + 1);
            // self.render(None);
        }
        unreachable!()
    }
    fn part2(&mut self) -> Self::Output2 {
        for power in 4.. {
            if let Some(n) = self.clone().experiment(power) {
                // dbg!(power);
                return n;
            }
        }
        unreachable!()
    }
}

impl Puzzle {
    fn experiment(mut self, power: usize) -> Option<usize> {
        let elves = self.creatures.iter().filter(|c| c.is_elf()).count();
        self.elf_power = power;
        for turn in 0.. {
            self.creatures.sort();
            let mut creatures = self.creatures.clone();
            for c in creatures.iter_mut() {
                if !c.exists_on(&self) {
                    continue;
                }
                if c.target_creatures(&self).is_empty() {
                    // println!("On turn {}, ", turn + 1);
                    debug_assert!(self.creatures.iter().all(|c| 0 < c.hit_point()));
                    let hit_points = self.creatures.iter().map(|c| c.hit_point()).sum::<usize>();
                    return Some(turn * hit_points);
                }
                c.turn(&mut self);
                if self.creatures.iter().filter(|c| c.is_elf()).count() != elves {
                    return None;
                }
            }
        }
        unreachable!()
    }
}
