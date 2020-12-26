use crate::{ProblemObject, ProblemSolver};
// use std::collections::HashMap;

pub fn template(part: usize, buffer: String) {
    if part == 1 {
        dbg!(World::parse(&buffer).part1());
    } else {
        dbg!(World::parse(&buffer).part2());
    }
}

#[derive(Debug, PartialEq)]
struct Object {}

impl ProblemObject for Object {
    fn parse(_s: &str) -> Option<Box<Self>> {
        todo!()
    }
}

#[derive(Debug, PartialEq)]
struct World {}

impl ProblemSolver for World {
    type TargetObject = Object;
    type Output1 = usize;
    type Output2 = String;
    fn add(&mut self, _object: Self::TargetObject) {
        todo!()
    }
    fn default() -> Self {
        World {}
    }
    fn parse(buffer: &str) -> World {
        let mut w = Self::default();
        for l in buffer.split('\n') {
            if let Some(d) = Self::TargetObject::parse(l) {
                w.add(*d);
            }
        }
        w
    }
    fn part1(&mut self) -> Self::Output1 {
        0
    }
    fn part2(&mut self) -> Self::Output2 {
        "done".to_string()
    }
}

mod test {
    use super::*;

    #[test]
    fn test_part1() {
        const TEST1: &str = "0\n1\n2";
        assert_eq!(World::parse(TEST1).part1(), 0);
    }
    #[test]
    fn test_part2() {
        const TEST2: &str = "0\n1\n2";
        assert_eq!(World::parse(TEST2).part2(), "done".to_string());
    }
}
