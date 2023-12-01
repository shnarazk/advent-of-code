//! <https://adventofcode.com/2018/day/24>
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        regex,
    },
    std::collections::{HashMap, HashSet},
};

#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
enum AttackType {
    Bludgeoning,
    Cold,
    Fire,
    Radiation,
    #[default]
    Slashing,
}

impl TryFrom<&str> for AttackType {
    type Error = ();
    fn try_from(value: &str) -> Result<Self, Self::Error> {
        match value {
            "cold" => Ok(AttackType::Cold),
            "bludgeoning" => Ok(AttackType::Bludgeoning),
            "fire" => Ok(AttackType::Fire),
            "radiation" => Ok(AttackType::Radiation),
            "slashing" => Ok(AttackType::Slashing),
            _ => Err(()),
        }
    }
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct Group {
    id: isize,
    units: usize,
    hitpoints: usize,
    weak_to: HashSet<AttackType>,
    immune_to: HashSet<AttackType>,
    attack: AttackType,
    damage: usize,
    initiative: usize,
}

impl Group {
    fn killed(&self) -> bool {
        self.units == 0
    }
    fn effective_power(&self) -> usize {
        self.units * self.damage
    }
    fn effective_damage(&self, target: &Group) -> usize {
        let p = self.effective_power();
        match (
            target.weak_to.contains(&self.attack),
            target.immune_to.contains(&self.attack),
        ) {
            (true, true) => panic!(),
            (true, false) => p * 2,
            (false, true) => 0,
            _ => p,
        }
    }
}

impl PartialOrd for Group {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        match other.effective_power().partial_cmp(&self.effective_power()) {
            Some(std::cmp::Ordering::Equal) => other.initiative.partial_cmp(&self.initiative),
            e => e,
        }
    }
}

impl Ord for Group {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        match other.effective_power().cmp(&self.effective_power()) {
            std::cmp::Ordering::Equal => other.initiative.cmp(&self.initiative),
            e => e,
        }
    }
}

#[test]
fn y2018day24effective_power() {
    let g = Group {
        units: 18,
        hitpoints: 729,
        attack: AttackType::Radiation,
        damage: 8,
        initiative: 10,
        ..Group::default()
    };
    assert_eq!(g.effective_power(), 144);
    let h = Group {
        units: 8,
        hitpoints: 729,
        attack: AttackType::Radiation,
        damage: 2,
        initiative: 10,
        ..Group::default()
    };
    let i = Group {
        units: 8,
        hitpoints: 729,
        attack: AttackType::Radiation,
        damage: 2,
        initiative: 100,
        ..Group::default()
    };
    assert!(g < h);
    assert!(i < h);
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Puzzle {
    immune: Vec<Group>,
    infection: Vec<Group>,
    reading_type_is_immune: bool,
}

type TargetList = HashMap<isize, isize>;

impl Puzzle {
    fn remains(&self) -> usize {
        self.immune.iter().map(|g| g.units).sum::<usize>()
            + self.infection.iter().map(|g| g.units).sum::<usize>()
    }
    fn got_happy_end(&self) -> Option<bool> {
        match (
            0 == self.immune.iter().filter(|g| !g.killed()).count(),
            0 == self.infection.iter().filter(|g| !g.killed()).count(),
        ) {
            (true, true) => panic!(),
            (true, false) => Some(false),
            (false, true) => Some(true),
            (false, false) => None,
        }
    }
    fn get(&self, id: isize) -> &Group {
        // id starts from one (not zero),
        if 0 < id {
            &self.immune[id as usize - 1]
        } else {
            &self.infection[(-id) as usize - 1]
        }
    }
    fn get_mut(&mut self, id: isize) -> &mut Group {
        // id starts from one (not zero),
        if 0 < id {
            &mut self.immune[id as usize - 1]
        } else {
            &mut self.infection[(-id) as usize - 1]
        }
    }
    fn build_targets(&self, attackers: &[Group], targets: &[Group]) -> TargetList {
        let mut target_list: TargetList = HashMap::new();
        let mut a = attackers.to_vec();
        a.sort();
        for attacker in a.iter() {
            if attacker.killed() {
                continue;
            }
            let mut best_target: Option<&Group> = None;
            let mut best_damage = 0;
            for target in targets
                .iter()
                .filter(|t| target_list.values().all(|id| *id != t.id))
            {
                if target.killed() {
                    continue;
                }
                let real_damage = attacker.effective_damage(target);
                if real_damage == 0 {
                    continue;
                }
                if best_damage < real_damage
                    || (best_damage == real_damage
                        && (best_target == None
                            || (best_target.unwrap().effective_power() < target.effective_power()
                                || (best_target.unwrap().effective_power()
                                    == target.effective_power()
                                    && best_target.unwrap().initiative < target.initiative))))
                {
                    best_damage = real_damage;
                    best_target = Some(target);
                }
            }
            if let Some(t) = best_target {
                target_list.insert(attacker.id, t.id);
            }
        }
        target_list
    }
    fn target_selection(&mut self) -> (TargetList, TargetList) {
        // self.sort_by_effective_power();
        (
            self.build_targets(&self.immune, &self.infection),
            self.build_targets(&self.infection, &self.immune),
        )
    }
    fn attacking(&mut self, matching: (TargetList, TargetList), log: bool) {
        let mut groups = self.immune.clone();
        groups.append(&mut self.infection.clone());
        groups.sort_by_key(|g| -(g.initiative as isize));
        let ids = groups.iter().map(|g| g.id).collect::<Vec<_>>();
        for attacker_id in ids.iter() {
            if let Some(target_id) = if 0 < *attacker_id {
                matching.0.get(attacker_id)
            } else {
                matching.1.get(attacker_id)
            } {
                let attacker = self.get(*attacker_id);
                assert_eq!(*attacker_id, attacker.id);
                if attacker.killed() {
                    continue;
                }
                let target = self.get(*target_id);
                assert_eq!(*target_id, target.id);
                if target.killed() {
                    continue;
                }
                let damage = attacker.effective_damage(target);
                let mut n_kill = damage / target.hitpoints;
                let target = self.get_mut(*target_id);
                let mut destoried = false;
                if target.units <= n_kill {
                    n_kill = target.units;
                    target.units = 0;
                    destoried = true;
                } else {
                    target.units -= n_kill;
                }
                let attacker = self.get(*attacker_id);
                if log {
                    println!(
                        "Group {}({} units) attacks deal defending group {}, killing {}{} units",
                        attacker.id,
                        attacker.units,
                        target_id,
                        if destoried { "all " } else { "" },
                        n_kill
                    );
                }
            }
        }
    }
}

#[aoc(2018, 24)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        // 801 units each with 4706 hit points (weak to radiation) with an attack that does 116 bludgeoning damage at initiative 1
        // 4485 units each with 2961 hit points (immune to radiation; weak to fire, cold) with an attack that does 12 slashing damage at initiative 4
        let set_type = regex!("^(Immune System:|Infection:|)$");
        if let Some(set_type) = set_type.captures(block) {
            match &set_type[1] {
                "Immune System:" => {
                    self.reading_type_is_immune = true;
                }
                "Infection:" => {
                    self.reading_type_is_immune = false;
                }
                _ => (),
            }
            return Ok(());
        }
        let parser = regex!(
            r"^(\d+) units each with (\d+) hit points( \([^)]+\))? with an attack that does (\d+) (\w+) damage at initiative (\d+)$"
        );
        let segment = parser.captures(block).ok_or(ParseError)?;
        // dbg!(&segment);
        let mut weak_to: HashSet<AttackType> = HashSet::new();
        let mut immune_to: HashSet<AttackType> = HashSet::new();
        if let Some(attrs) = segment.get(3) {
            for attr in attrs.as_str().split(';') {
                let target = attr.trim().trim_matches('(').trim_matches(')');
                let parser2 = regex!(r"(weak|immune) to (.*)$");
                let attributes = parser2.captures(target).ok_or(ParseError)?;
                if &attributes[1] == "weak" {
                    for word in attributes[2].split(", ") {
                        weak_to.insert(AttackType::try_from(word).unwrap());
                    }
                } else {
                    for word in attributes[2].split(", ") {
                        immune_to.insert(AttackType::try_from(word).unwrap());
                    }
                }
            }
        }
        if self.reading_type_is_immune {
            self.immune.push(Group {
                id: (self.immune.len() + 1) as isize,
                units: segment[1].parse::<usize>()?,
                hitpoints: segment[2].parse::<usize>()?,
                weak_to,
                immune_to,
                attack: AttackType::try_from(&segment[5]).map_err(|_| ParseError)?,
                damage: segment[4].parse::<usize>()?,
                initiative: segment[6].parse::<usize>()?,
            });
        } else {
            self.infection.push(Group {
                id: -((self.infection.len() + 1) as isize),
                units: segment[1].parse::<usize>()?,
                hitpoints: segment[2].parse::<usize>()?,
                weak_to,
                immune_to,
                attack: AttackType::try_from(&segment[5]).map_err(|_| ParseError)?,
                damage: segment[4].parse::<usize>()?,
                initiative: segment[6].parse::<usize>()?,
            });
        }
        Ok(())
    }
    fn end_of_data(&mut self) {
        dbg!(&self.immune.len());
        dbg!(&self.infection.len());
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut remains = self.remains();
        let mut stag = 0;
        loop {
            let list = self.target_selection();
            self.attacking(list, 97 < stag);
            if 97 < stag {
                println!(
                    "### Immute remains {} groups, Infection remains {} groups.",
                    self.immune.iter().filter(|g| !g.killed()).count(),
                    self.infection.iter().filter(|g| !g.killed()).count()
                );
            }
            if self.immune.iter().filter(|g| !g.killed()).count() == 0
                || self.infection.iter().filter(|g| !g.killed()).count() == 0
            {
                break;
            }
            let tmp = self.remains();
            if remains == tmp {
                stag += 1;
                if 100 < stag {
                    // let i1 = self
                    //     .immune
                    //     .iter()
                    //     .filter(|g| 0 < g.units)
                    //     .collect::<Vec<_>>();
                    // let i2 = self
                    //     .infection
                    //     .iter()
                    //     .filter(|g| 0 < g.units)
                    //     .collect::<Vec<_>>();
                    // dbg!(i1, i2);
                    return 0;
                }
            } else {
                stag = 0;
            }
            remains = tmp;
        }
        // dbg!(self.immune.iter().filter(|g| !g.killed()).count());
        // dbg!(self.infection.iter().filter(|g| !g.killed()).count());
        // dbg!(self.immune.iter().map(|g| g.units).sum::<usize>());
        // dbg!(self.infection.iter().map(|g| g.units).sum::<usize>());
        self.immune.iter().map(|g| g.units).sum::<usize>()
            + self.infection.iter().map(|g| g.units).sum::<usize>()
    }
    fn part2(&mut self) -> Self::Output2 {
        // let mut ng = 70;
        // let mut ok = 1000;
        let mut units = 0;
        // while ng + 1 < ok {
        // for med in 1568..1574 {
        for med in 1..80 {
            let mut w = self.clone();
            // let med = (ng + ok) / 2;
            for g in w.immune.iter_mut() {
                g.damage += med;
            }
            let tmp = w.part1();
            if let Some(result) = w.got_happy_end() {
                if result {
                    println!("ok at {med}, {tmp}");
                    // ok = med;
                    units = tmp;
                } else {
                    println!("no at {med}, {tmp}");
                    // ng = m, 95 < staged;
                }
            } else if tmp == 0 {
                println!(
                    "loop at {med}, {}",
                    w.immune.iter().map(|g| g.units).sum::<usize>()
                );
                // ng = med;
            } else {
                panic!();
            }
            // dbg!(ng, ok, tmp);
        }
        units
    }
}
