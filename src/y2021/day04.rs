//! <https://adventofcode.com/2021/day/4>
use {
    crate::framework::{aoc, AdventOfCode, ParseError},
    std::borrow::Cow,
};

type Board = Vec<Vec<usize>>;

#[derive(Clone, Debug, Default)]
pub struct Puzzle {
    hands: Vec<usize>,
    board: Vec<Board>,
    order: Vec<usize>,
    num_col: usize,
    num_row: usize,
}

fn col_at(vec: &[Vec<usize>], at: usize) -> Cow<Vec<usize>> {
    Cow::Owned(vec.iter().map(|l| l[at]).collect::<Vec<usize>>())
}

fn row_at(vec: &[Vec<usize>], at: usize) -> Cow<Vec<usize>> {
    Cow::Borrowed(&vec[at])
}

fn grade(vec: &[usize], order: &[usize], board: &[Vec<usize>]) -> Option<(usize, usize)> {
    let mut need = 0;
    for i in vec.iter() {
        if let Some(o) = order.get(*i) {
            need = need.max(*o);
        } else {
            return None;
        }
    }
    let point = board
        .iter()
        .map(|v| {
            v.iter()
                .map(|n| if order[*n] <= need { 0 } else { *n })
                .sum::<usize>()
        })
        .sum();
    Some((need, point))
}

mod parser {
    use {
        super::Board,
        crate::parser::parse_usize,
        winnow::{
            ascii::{newline, space0, space1},
            combinator::{preceded, separated, seq},
            PResult, Parser,
        },
    };

    fn parse_sequence(s: &mut &str) -> PResult<Vec<usize>> {
        separated(1.., parse_usize, ",").parse_next(s)
    }

    fn parse_bingo(s: &mut &str) -> PResult<Board> {
        separated(
            5..=5,
            preceded(
                space0,
                separated::<_, _, Vec<usize>, _, _, _, _>(5..=5, parse_usize, space1),
            ),
            newline,
        )
        .parse_next(s)
    }

    pub fn parse(s: &mut &str) -> PResult<(Vec<usize>, Vec<Board>)> {
        seq!(
            parse_sequence,
            _: (newline, newline),
            separated(1.., parse_bingo, (newline, newline))
        )
        .parse_next(s)
    }
}

#[aoc(2021, 4)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, input: String) -> Result<String, ParseError> {
        let (hands, boards) = parser::parse(&mut input.as_str())?;
        self.hands = hands;
        self.board = boards;
        Self::parsed()
    }
    fn end_of_data(&mut self) {
        self.num_col = self.board[0][0].len();
        self.num_row = self.board[0].len();
        self.order.clone_from(&self.hands);
        for (i, h) in self.hands.iter().enumerate() {
            self.order[*h] = i;
        }
    }
    fn part1(&mut self) -> usize {
        let x: Vec<(usize, usize)> = self
            .board
            .iter()
            .flat_map(|b| {
                (0..self.num_row)
                    .flat_map(|i| {
                        [
                            grade(&row_at(b, i), &self.order, b),
                            grade(&col_at(b, i), &self.order, b),
                        ]
                    })
                    .flatten()
                    .collect::<Vec<_>>()
            })
            .collect();
        let result = x.iter().min_by_key(|(h, _)| h).expect("??");
        self.hands[result.0] * result.1
    }
    fn part2(&mut self) -> usize {
        let x: Vec<(usize, usize)> = self
            .board
            .iter()
            .map(|b| {
                (0..self.num_row)
                    .flat_map(|i| {
                        [
                            grade(&row_at(b, i), &self.order, b),
                            grade(&col_at(b, i), &self.order, b),
                        ]
                    })
                    .flatten()
                    .min_by_key(|(h, _)| *h)
                    .expect("??")
            })
            .collect();
        let result = x.iter().max_by_key(|(h, _)| h).expect("??");
        self.hands[result.0] * result.1
    }
}
