//! <https://adventofcode.com/2017/day/25>
use {
    crate::framework::{aoc_at, AdventOfCode, ParseError},
    std::collections::HashMap,
};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Rule {
    current_state: u8,
    current_value: usize,
    output: usize,
    move_forward: bool, // forward means 'right'
    next_state: u8,
}

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Rule>,
    step: usize,
}

#[aoc_at(2017, 25)]
impl AdventOfCode for Puzzle {
    type Output1 = usize;
    type Output2 = String;
    const DELIMITER: &'static str = "\n";
    fn parse_block(&mut self, _: &str) -> Result<(), ParseError> {
        Ok(())
    }
    fn end_of_data(&mut self) {
        // Begin in state A.
        // Perform a diagnostic checksum after 12172063 steps.
        self.step = 12172063;

        // In state A:
        //   If the current value is 0:
        //     - Write the value 1.
        //     - Move one slot to the right.
        //     - Continue with state B.
        self.line.push(Rule {
            current_state: b'A',
            current_value: 0,
            output: 1,
            move_forward: true, // forward means 'right'
            next_state: b'B',
        });
        //   If the current value is 1:
        //     - Write the value 0.
        //     - Move one slot to the left.
        //     - Continue with state C.
        self.line.push(Rule {
            current_state: b'A',
            current_value: 1,
            output: 0,
            move_forward: false, // forward means 'right'
            next_state: b'C',
        });

        // In state B:
        //   If the current value is 0:
        //     - Write the value 1.
        //     - Move one slot to the left.
        //     - Continue with state A.
        self.line.push(Rule {
            current_state: b'B',
            current_value: 0,
            output: 1,
            move_forward: false,
            next_state: b'A',
        });
        //   If the current value is 1:
        //     - Write the value 1.
        //     - Move one slot to the left.
        //     - Continue with state D.
        self.line.push(Rule {
            current_state: b'B',
            current_value: 1,
            output: 1,
            move_forward: false,
            next_state: b'D',
        });

        // In state C:
        //   If the current value is 0:
        //     - Write the value 1.
        //     - Move one slot to the right.
        //     - Continue with state D.
        self.line.push(Rule {
            current_state: b'C',
            current_value: 0,
            output: 1,
            move_forward: true,
            next_state: b'D',
        });
        //   If the current value is 1:
        //     - Write the value 0.
        //     - Move one slot to the right.
        //     - Continue with state C.
        self.line.push(Rule {
            current_state: b'C',
            current_value: 1,
            output: 0,
            move_forward: true,
            next_state: b'C',
        });

        // In state D:
        //   If the current value is 0:
        //     - Write the value 0.
        //     - Move one slot to the left.
        //     - Continue with state B.
        self.line.push(Rule {
            current_state: b'D',
            current_value: 0,
            output: 0,
            move_forward: false,
            next_state: b'B',
        });
        //   If the current value is 1:
        //     - Write the value 0.
        //     - Move one slot to the right.
        //     - Continue with state E.
        self.line.push(Rule {
            current_state: b'D',
            current_value: 1,
            output: 0,
            move_forward: true,
            next_state: b'E',
        });

        // In state E:
        //   If the current value is 0:
        //     - Write the value 1.
        //     - Move one slot to the right.
        //     - Continue with state C.
        self.line.push(Rule {
            current_state: b'E',
            current_value: 0,
            output: 1,
            move_forward: true,
            next_state: b'C',
        });
        //   If the current value is 1:
        //     - Write the value 1.
        //     - Move one slot to the left.
        //     - Continue with state F.
        self.line.push(Rule {
            current_state: b'E',
            current_value: 1,
            output: 1,
            move_forward: false,
            next_state: b'F',
        });

        // In state F:
        //   If the current value is 0:
        //     - Write the value 1.
        //     - Move one slot to the left.
        //     - Continue with state E.
        self.line.push(Rule {
            current_state: b'F',
            current_value: 0,
            output: 1,
            move_forward: false,
            next_state: b'E',
        });
        //   If the current value is 1:
        //     - Write the value 1.
        //     - Move one slot to the right.
        //     - Continue with state A.
        self.line.push(Rule {
            current_state: b'F',
            current_value: 1,
            output: 1,
            move_forward: true,
            next_state: b'A',
        });
        // dbg!(&self.line);
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut tape: HashMap<isize, usize> = HashMap::new();
        let mut cursor: isize = 0;
        let mut state: u8 = b'A';
        for _ in 0..self.step {
            if let Some(rule) = self.line.iter().find(|&r| {
                r.current_state == state && *tape.get(&cursor).unwrap_or(&0) == r.current_value
            }) {
                tape.insert(cursor, rule.output);
                cursor += 2 * (rule.move_forward as isize) - 1;
                state = rule.next_state;
            }
        }
        tape.values().sum::<usize>()
    }
    fn part2(&mut self) -> Self::Output2 {
        "Happy holidays!".to_string()
    }
}
