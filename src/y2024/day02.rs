//! <https://adventofcode.com/2024/day/2>
use {
    crate::framework::{aoc, AdventOfCode, ParseError},
    nom::{
        character::complete::{newline, space1, u64},
        multi::{many1, separated_list1},
        sequence::terminated,
        IResult,
    },
    serde::Serialize,
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
pub struct Puzzle {
    line: Vec<Vec<u64>>,
}

fn parse_line(str: &str) -> IResult<&str, Vec<u64>> {
    separated_list1(space1, u64)(str)
}

#[aoc(2024, 2)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, input: String) -> Result<String, ParseError> {
        let (_, v): (&str, Vec<Vec<u64>>) = many1(terminated(parse_line, newline))(input.as_str())?;
        self.line = v;
        Ok("".to_string())
    }
    fn part1(&mut self) -> Self::Output1 {
        self.line
            .iter()
            .filter(|levels| {
                (levels.windows(2).all(|v| v[0] < v[1]) || levels.windows(2).all(|v| v[0] > v[1]))
                    && levels.windows(2).all(|v| {
                        let d = v[0].abs_diff(v[1]);
                        1 <= d && d <= 3
                    })
            })
            .count()
    }
    fn part2(&mut self) -> Self::Output2 {
        self.line
            .iter()
            .filter(|ls| {
                for (i, _) in ls.iter().enumerate() {
                    let mut levels = (*ls).clone();
                    levels.remove(i);
                    if (levels.windows(2).all(|v| v[0] < v[1])
                        || levels.windows(2).all(|v| v[0] > v[1]))
                        && levels.windows(2).all(|v| {
                            let d = v[0].abs_diff(v[1]);
                            1 <= d && d <= 3
                        })
                    {
                        return true;
                    }
                }
                false
            })
            .count()
    }
}
