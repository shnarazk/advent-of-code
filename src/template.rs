use crate::{ProblemObject, ProblemSolver};
use std::collections::HashMap;

pub fn day00(part: usize, buffer: String) {
    if part == 1 {
        dbg!(World::parse(buffer).part1());
    } else {
        dbg!(World::parse(buffer).part2());
    }
}

#[derive(Debug, PartialEq)]
struct Object {
}

impl ProblemObject for Object {
    fn parse(s: &str) -> Option<Box<Self>> {
        todo!()
    }
}

#[derive(Debug, PartialEq)]
struct World {
}

impl ProblemSolver for World {
    type TargetObject = Object;
    type Output = usize;
    fn add(&mut self, object: Self::TargetObject) {
        todo!()
    }
    fn default() -> Self {
        World {}
    } 
    fn parse(buffer: String) -> World {
        let mut w = Self::default();
        for l in buffer.split('\n') {
            if let Some(d) = Self::TargetObject::parse(l) {
                w.add(*d);
            }
        }
        w
    }
    fn part1(&mut self) -> Self::Output {
        todo!()
    }
    fn part2(&mut self) -> Self::Output {
        todo!()
    }
}

mod test {
    use super::*;

    #[test]
    fn test_part1() {
        const TEST1: &str = "0\n1\n2";
        assert_eq!(Dic::from(TEST1).part1(), 123);
    }
    #[test]
    fn test_part2() {
        const TEST2: &str = "0\n1\n2";
        assert_eq!(Dic::from(TEST2).part2(), 123);
    }
}
