//! <https://adventofcode.com/2018/day/24>
use {
    crate::framework::{aoc, AdventOfCode, ParseError},
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
        Some(self.cmp(other))
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
                        && (best_target.is_none()
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
                debug_assert_eq!(*attacker_id, attacker.id);
                if attacker.killed() {
                    continue;
                }
                let target = self.get(*target_id);
                debug_assert_eq!(*target_id, target.id);
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

mod parser {
    use {
        super::*,
        crate::parser::parse_usize,
        std::collections::HashSet,
        winnow::{
            ascii::newline,
            combinator::{alt, separated, seq},
            ModalResult, Parser,
        },
    };

    fn parse_attack_type(s: &mut &str) -> ModalResult<AttackType> {
        alt((
            "cold".value(AttackType::Cold),
            "bludgeoning".value(AttackType::Bludgeoning),
            "fire".value(AttackType::Fire),
            "radiation".value(AttackType::Radiation),
            "slashing".value(AttackType::Slashing),
        ))
        .parse_next(s)
    }

    fn parse_property_block1(s: &mut &str) -> ModalResult<(bool, HashSet<AttackType>)> {
        alt((
            seq!(_: "weak to ", separated(1.., parse_attack_type, ", ").map(|v: Vec<AttackType>| v)).map(|(v,)| (false, v.into_iter().collect::<HashSet<AttackType>>())),
            seq!(_: "immune to ", separated(1.., parse_attack_type, ", ").map(|v: Vec<AttackType>| v)).map(|(v,)| (true, v.into_iter().collect::<HashSet<AttackType>>())),
        )).parse_next(s)
    }

    fn parse_property_block(
        s: &mut &str,
    ) -> ModalResult<(HashSet<AttackType>, HashSet<AttackType>)> {
        alt((
            seq!(
                _: " (",
                separated(1.., parse_property_block1, "; ").map(|v: Vec<(bool, HashSet<AttackType>)>| {
                    let v1 = v.iter().find(|(b, _)| !b).map_or(HashSet::new(), |(_, e)| e.clone());
                    let v2 = v.iter().find(|(b, _)| *b).map_or(HashSet::new(), |(_, e)| e.clone());
                    (v1, v2)
                }),
                _: ") ")
                .map(|(h,)| h),
            " ".value((HashSet::new(), HashSet::new())),
        ))
        .parse_next(s)
    }

    fn parse_group(s: &mut &str) -> ModalResult<Group> {
        seq!(
            parse_usize,
            _: " units each with ", parse_usize,
            _: " hit points",
            parse_property_block,
            _: "with an attack that does ", parse_usize,
            _: " ",  parse_attack_type,
           _: " damage at initiative ", parse_usize)
        .map(
            |(units, hitpoints, (weak_to, immune_to), damage, attack_type, initiative)| Group {
                id: 0,
                units,
                hitpoints,
                weak_to,
                immune_to,
                damage,
                attack: attack_type,
                initiative,
            },
        )
        .parse_next(s)
    }

    pub fn parse(s: &mut &str) -> ModalResult<(Vec<Group>, Vec<Group>)> {
        seq!(
            _: "Immune System:\n", separated(1.., parse_group, newline),
            _: "\n\nInfection:\n", separated(1.., parse_group, newline)
        )
        .map(|(immunes, infections): (Vec<Group>, Vec<Group>)| {
            (
                immunes
                    .iter()
                    .enumerate()
                    .map(|(i, g)| Group {
                        id: i as isize + 1,
                        ..g.clone()
                    })
                    .collect(),
                infections
                    .iter()
                    .enumerate()
                    .map(|(i, g)| Group {
                        id: -(i as isize) - 1,
                        ..g.clone()
                    })
                    .collect(),
            )
        })
        .parse_next(s)
    }
}

#[aoc(2018, 24)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, input: String) -> Result<String, ParseError> {
        let (immunes, infections) = parser::parse(&mut input.as_str())?;
        self.immune = immunes;
        self.infection = infections;
        dbg!(&self.immune.len());
        dbg!(&self.infection.len());
        Self::parsed()
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut remains = self.remains();
        let mut stag = 0;
        loop {
            let list = self.target_selection();
            self.attacking(list, false /* 97 < stag */);
            // if 97 < stag {
            //     println!(
            //         "### Immute remains {} groups, Infection remains {} groups.",
            //         self.immune.iter().filter(|g| !g.killed()).count(),
            //         self.infection.iter().filter(|g| !g.killed()).count()
            //     );
            // }
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
        // while ng + 1 < ok {
        // for med in 1568..1574 {
        for boost in 1..80 {
            let mut w = self.clone();
            // let med = (ng + ok) / 2;
            for g in w.immune.iter_mut() {
                g.damage += boost;
            }
            let tmp = w.part1();
            if let Some(result) = w.got_happy_end() {
                if result {
                    // println!("ok at {boost}, {tmp}");
                    // ok = med;
                    return tmp;
                } else {
                    // println!("no at {boost}, {tmp}");
                    // ng = m, 95 < staged;
                }
            } else if tmp == 0 {
                // println!(
                //     "loop at {boost}, {}",
                //     w.immune.iter().map(|g| g.units).sum::<usize>()
                // );
                // ng = med;
            } else {
                panic!();
            }
            // dbg!(ng, ok, tmp);
        }
        unreachable!()
    }
}
