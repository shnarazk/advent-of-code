import Std
import Lean.Data.Parsec
import «AoC».Basic
import «AoC».Parser

namespace Day07

structure Hand where
  hand ::
  cards : Array Char
  bid   : Nat
deriving Inhabited, Repr

namespace parser
open Lean Parsec AoCParser

def card := digit <|> pchar 'A' <|> pchar 'K' <|> pchar 'Q' <|> pchar 'J' <|> pchar 'T'

def cards := many1 card <* whitespaces

def line : Parsec Hand := (pure Hand.hand) <*> cards <*> number

def parser := sepBy1 line eol

end parser

def solve1_line (_line : String) : Nat := 0

def uniqueChars (cs : Array Char) : List Char :=
  Array.foldl (fun l e => if l.contains e then l else e :: l) [] cs

def occurences (cs : Array Char) : Array Nat :=
  List.map (fun c => (Array.filter (. == c) cs).size) (uniqueChars cs)
    |> List.toArray
    |> Array.qsortOrd
    |> Array.reverse

#eval occurences #['A', '3', '9', 'A', 'A']

def evaluation (h : Hand) : Nat × Nat :=
  match occurences h.cards with
  | #[5]          => (7, h.bid) -- Five of a kind
  | #[4, 1]       => (6, h.bid) -- Four of a kind
  | #[3, 2]       => (5, h.bid) -- Full house
  | #[3, 1, 1]    => (4, h.bid) -- Three of a kind
  | #[2, 2, 1]    => (3, h.bid) -- Two pair
  | #[2, 1, 1, 1] => (2, h.bid) -- One pair
  | _             => (1, h.bid) -- High card

#eval evaluation $ Hand.hand #['A', '3', '9', 'A', 'A'] 33

def solve1 (data : String) : IO Unit := do
  match AoCParser.parse parser.parser data with
  | none   => IO.println s!"  part1: parse error"
  | some d =>
    let test := d[0]!
    IO.println s!"{evaluation test}"
    IO.println s!"  part1: {d.size}"
  return ()

def solve2_line (_line : String) : Nat := 0

def solve2 (_lines : String) : IO Unit := do
  let sum := 0
  IO.println s!"  part2: {sum}"
  return ()

end Day07

def day07 (ext : Option String) : IO Unit := do
  let data ← dataOf 2023 7 ext
  pure data >>= Day07.solve1
  pure data >>= Day07.solve2
